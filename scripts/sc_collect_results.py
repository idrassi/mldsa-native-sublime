#!/usr/bin/env python3
import argparse
import csv
import os
import re
import sys


def parse_histogram(lines, start_idx):
  hist = {}
  for line in lines[start_idx + 1 :]:
    line = line.strip()
    if not line.startswith("kappa"):
      break
    m = re.match(r"kappa(>=16|=\d+):\s+(\d+)", line)
    if not m:
      continue
    bucket = m.group(1)
    bucket = ">=16" if bucket == ">=16" else bucket.split("=")[1]
    hist[bucket] = int(m.group(2))
  return hist


def parse_rejects(line):
  m = re.findall(r"([zh]|w0|hint)=(\d+)", line)
  out = {"z": 0, "w0": 0, "h": 0, "hint": 0}
  for key, val in m:
    out[key] = int(val)
  return out


def parse_log(path):
  with open(path, encoding="utf-8") as f:
    lines = f.read().splitlines()

  param_set = None
  nstat = None
  baseline_mean = None
  channel_mean = None
  baseline_rejects = None
  channel_rejects = None
  baseline_hist = None
  channel_hist = None

  for idx, line in enumerate(lines):
    if line.startswith("param_set="):
      param_set = line.split("=", 1)[1].strip()
    if line.startswith("Abort stats"):
      m = re.search(r"nstat=(\d+)", line)
      if m:
        nstat = int(m.group(1))
    if line.strip().startswith("baseline mean attempts"):
      m = re.search(r"([\d.]+)$", line.strip())
      if m:
        baseline_mean = float(m.group(1))
    if line.strip().startswith("channel  mean attempts"):
      m = re.search(r"([\d.]+)$", line.strip())
      if m:
        channel_mean = float(m.group(1))
    if line.strip().startswith("baseline rejects"):
      baseline_rejects = parse_rejects(line)
    if line.strip().startswith("channel  rejects"):
      channel_rejects = parse_rejects(line)
    if line.strip() == "baseline kappa histogram:":
      baseline_hist = parse_histogram(lines, idx)
    if line.strip() == "channel  kappa histogram:":
      channel_hist = parse_histogram(lines, idx)

  if param_set is None:
    m = re.search(r"(\d{2})", os.path.basename(path))
    if m:
      param_set = m.group(1)

  missing = []
  for name, val in (
      ("param_set", param_set),
      ("nstat", nstat),
      ("baseline_mean", baseline_mean),
      ("channel_mean", channel_mean),
      ("baseline_rejects", baseline_rejects),
      ("channel_rejects", channel_rejects),
      ("baseline_hist", baseline_hist),
      ("channel_hist", channel_hist),
  ):
    if val is None:
      missing.append(name)

  if missing:
    raise ValueError(f"{path}: missing fields: {', '.join(missing)}")

  return {
      "param_set": param_set,
      "nstat": nstat,
      "baseline_mean": baseline_mean,
      "channel_mean": channel_mean,
      "baseline_rejects": baseline_rejects,
      "channel_rejects": channel_rejects,
      "baseline_hist": baseline_hist,
      "channel_hist": channel_hist,
  }


def write_summary(rows, out_path):
  fieldnames = [
      "param_set",
      "nstat",
      "baseline_mean_attempts",
      "channel_mean_attempts",
      "baseline_reject_z",
      "baseline_reject_w0",
      "baseline_reject_h",
      "baseline_reject_hint",
      "channel_reject_z",
      "channel_reject_w0",
      "channel_reject_h",
      "channel_reject_hint",
  ]
  with open(out_path, "w", newline="", encoding="utf-8") as f:
    writer = csv.DictWriter(f, fieldnames=fieldnames)
    writer.writeheader()
    for row in rows:
      writer.writerow({
          "param_set": row["param_set"],
          "nstat": row["nstat"],
          "baseline_mean_attempts": row["baseline_mean"],
          "channel_mean_attempts": row["channel_mean"],
          "baseline_reject_z": row["baseline_rejects"]["z"],
          "baseline_reject_w0": row["baseline_rejects"]["w0"],
          "baseline_reject_h": row["baseline_rejects"]["h"],
          "baseline_reject_hint": row["baseline_rejects"]["hint"],
          "channel_reject_z": row["channel_rejects"]["z"],
          "channel_reject_w0": row["channel_rejects"]["w0"],
          "channel_reject_h": row["channel_rejects"]["h"],
          "channel_reject_hint": row["channel_rejects"]["hint"],
      })


def write_kappa(rows, out_path):
  buckets = [str(i) for i in range(1, 16)] + [">=16"]
  with open(out_path, "w", newline="", encoding="utf-8") as f:
    writer = csv.DictWriter(
        f, fieldnames=["param_set", "mode", "kappa_bucket", "count"]
    )
    writer.writeheader()
    for row in rows:
      for mode, hist in (
          ("baseline", row["baseline_hist"]),
          ("channel", row["channel_hist"]),
      ):
        for bucket in buckets:
          writer.writerow({
              "param_set": row["param_set"],
              "mode": mode,
              "kappa_bucket": bucket,
              "count": hist.get(bucket, 0),
          })


def parse_args():
  parser = argparse.ArgumentParser(
      description="Parse test_sc logs into summary/kappa CSVs."
  )
  parser.add_argument(
      "logs",
      nargs="+",
      help="Paths to test_sc logs (one per parameter set).",
  )
  parser.add_argument(
      "--out-dir",
      default="test/results/sc",
      help="Output directory (default: %(default)s)",
  )
  parser.add_argument(
      "--tag",
      default="opt1",
      help="Tag suffix for output CSVs (default: %(default)s)",
  )
  return parser.parse_args()


def main():
  args = parse_args()
  os.makedirs(args.out_dir, exist_ok=True)
  rows = []
  for path in args.logs:
    try:
      rows.append(parse_log(path))
    except Exception as exc:
      print(f"Failed to parse {path}: {exc}", file=sys.stderr)
      return 1

  summary_path = os.path.join(args.out_dir, f"summary_{args.tag}.csv")
  kappa_path = os.path.join(args.out_dir, f"kappa_counts_{args.tag}.csv")
  write_summary(rows, summary_path)
  write_kappa(rows, kappa_path)

  print(f"Wrote {summary_path}")
  print(f"Wrote {kappa_path}")
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
