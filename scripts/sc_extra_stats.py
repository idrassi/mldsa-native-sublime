#!/usr/bin/env python3
import argparse
import csv
import math
import os
import sys


def load_summary(path):
    data = {}
    with open(path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            param_set = row.get("param_set")
            if not param_set:
                continue
            data[param_set] = {
                "nstat": int(row["nstat"]),
                "baseline_mean": float(row["baseline_mean_attempts"]),
                "channel_mean": float(row["channel_mean_attempts"]),
                "baseline_reject_z": int(row["baseline_reject_z"]),
                "baseline_reject_w0": int(row["baseline_reject_w0"]),
                "baseline_reject_h": int(row["baseline_reject_h"]),
                "baseline_reject_hint": int(row["baseline_reject_hint"]),
                "channel_reject_z": int(row["channel_reject_z"]),
                "channel_reject_w0": int(row["channel_reject_w0"]),
                "channel_reject_h": int(row["channel_reject_h"]),
                "channel_reject_hint": int(row["channel_reject_hint"]),
            }
    return data


def load_kappa(path):
    data = {}
    with open(path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            param_set = row.get("param_set")
            mode = row.get("mode")
            bucket = row.get("kappa_bucket")
            count = int(row.get("count", 0))
            if not param_set or not mode or not bucket:
                continue
            data.setdefault(param_set, {}).setdefault(mode, {})[bucket] = count
    return data


def hist_stats(counts):
    values = list(range(1, 16)) + [16]
    total = sum(counts.values())
    if total == 0:
        return 0.0, 0.0
    mean = 0.0
    for v in values:
        key = ">=16" if v == 16 else str(v)
        mean += v * counts.get(key, 0)
    mean /= total
    var = 0.0
    for v in values:
        key = ">=16" if v == 16 else str(v)
        var += counts.get(key, 0) * (v - mean) ** 2
    var /= total
    return mean, var


def parse_args():
    parser = argparse.ArgumentParser(
        description="Compute extra SC stats from summary and kappa CSVs."
    )
    parser.add_argument(
        "--summary-csv",
        required=True,
        help="Path to summary CSV (e.g., summary_opt1_100k.csv)",
    )
    parser.add_argument(
        "--kappa-csv",
        required=True,
        help="Path to kappa_counts CSV (e.g., kappa_counts_opt1_100k.csv)",
    )
    parser.add_argument(
        "--out-dir",
        default="test/results/sc",
        help="Output directory (default: %(default)s)",
    )
    parser.add_argument(
        "--tag",
        default="opt1_100k",
        help="Tag for output filenames (default: %(default)s)",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    summary = load_summary(args.summary_csv)
    kappa = load_kappa(args.kappa_csv)
    if not summary:
        print("Summary CSV is empty", file=sys.stderr)
        return 1

    os.makedirs(args.out_dir, exist_ok=True)

    reject_rows = []
    kappa_rows = []

    for param_set, s in summary.items():
        nstat = s["nstat"]
        for mode in ("baseline", "channel"):
            if mode == "baseline":
                mean_attempts = s["baseline_mean"]
                rz = s["baseline_reject_z"]
                rw0 = s["baseline_reject_w0"]
                rh = s["baseline_reject_h"]
                rhint = s["baseline_reject_hint"]
            else:
                mean_attempts = s["channel_mean"]
                rz = s["channel_reject_z"]
                rw0 = s["channel_reject_w0"]
                rh = s["channel_reject_h"]
                rhint = s["channel_reject_hint"]

            rejects_total = rz + rw0 + rh + rhint
            attempts = nstat + rejects_total
            accept_rate = (nstat / attempts) if attempts else 0.0
            reject_rate = (rejects_total / attempts) if attempts else 0.0

            reject_rows.append(
                {
                    "param_set": param_set,
                    "mode": mode,
                    "nstat": nstat,
                    "attempts": attempts,
                    "rejects_total": rejects_total,
                    "accept_rate": accept_rate,
                    "reject_rate": reject_rate,
                    "reject_z_rate": (rz / attempts) if attempts else 0.0,
                    "reject_w0_rate": (rw0 / attempts) if attempts else 0.0,
                    "reject_h_rate": (rh / attempts) if attempts else 0.0,
                    "reject_hint_rate": (rhint / attempts) if attempts else 0.0,
                    "reject_z_share": (rz / rejects_total) if rejects_total else 0.0,
                    "reject_w0_share": (rw0 / rejects_total) if rejects_total else 0.0,
                    "reject_h_share": (rh / rejects_total) if rejects_total else 0.0,
                    "reject_hint_share": (rhint / rejects_total) if rejects_total else 0.0,
                }
            )

            counts = kappa.get(param_set, {}).get(mode, {})
            kappa_total = sum(counts.values())
            if kappa_total != nstat and kappa_total != 0:
                print(
                    f"Warning: kappa count mismatch for {param_set} {mode}: "
                    f"nstat={nstat}, hist_total={kappa_total}",
                    file=sys.stderr,
                )
            kappa_ge_16 = counts.get(">=16", 0)
            tail_prob = (kappa_ge_16 / nstat) if nstat else 0.0
            mean_hist, var_hist = hist_stats(counts)

            kappa_rows.append(
                {
                    "param_set": param_set,
                    "mode": mode,
                    "nstat": nstat,
                    "mean_attempts": mean_attempts,
                    "attempts": attempts,
                    "kappa_ge_16": kappa_ge_16,
                    "tail_prob": tail_prob,
                    "mean_from_hist": mean_hist,
                    "var_from_hist": var_hist,
                    "std_from_hist": math.sqrt(var_hist),
                    "note": "tail>=16->16",
                }
            )

    reject_path = os.path.join(args.out_dir, f"reject_rates_{args.tag}.csv")
    kappa_path = os.path.join(args.out_dir, f"kappa_summary_{args.tag}.csv")

    with open(reject_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "param_set",
                "mode",
                "nstat",
                "attempts",
                "rejects_total",
                "accept_rate",
                "reject_rate",
                "reject_z_rate",
                "reject_w0_rate",
                "reject_h_rate",
                "reject_hint_rate",
                "reject_z_share",
                "reject_w0_share",
                "reject_h_share",
                "reject_hint_share",
            ],
        )
        writer.writeheader()
        for row in reject_rows:
            writer.writerow(row)

    with open(kappa_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "param_set",
                "mode",
                "nstat",
                "mean_attempts",
                "attempts",
                "kappa_ge_16",
                "tail_prob",
                "mean_from_hist",
                "var_from_hist",
                "std_from_hist",
                "note",
            ],
        )
        writer.writeheader()
        for row in kappa_rows:
            writer.writerow(row)

    print(f"Wrote {reject_path}")
    print(f"Wrote {kappa_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
