#!/usr/bin/env python3
import argparse
import csv
import os
import sys


def load_kappa_counts(path):
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


def kappa_buckets():
    return [str(i) for i in range(1, 16)] + [">=16"]


def counts_to_probs(counts):
    buckets = kappa_buckets()
    values = [counts.get(b, 0) for b in buckets]
    total = sum(values)
    if total == 0:
        return [0.0] * len(values), total
    return [v / total for v in values], total


def cdf_from_probs(probs):
    cdf = []
    s = 0.0
    for p in probs:
        s += p
        cdf.append(s)
    return cdf


def ks_from_cdf(cdf_a, cdf_b):
    return max(abs(a - b) for a, b in zip(cdf_a, cdf_b))


def parse_args():
    parser = argparse.ArgumentParser(
        description=(
            "Plot ML-DSA SC kappa histograms and CDFs from kappa_counts CSV output."
        )
    )
    parser.add_argument(
        "--kappa-csv",
        default="test/results/sc/kappa_counts_opt1_100k.csv",
        help="Path to kappa_counts CSV (default: %(default)s)",
    )
    parser.add_argument(
        "--out-dir",
        default="test/results/sc/plots",
        help="Output directory for plots (default: %(default)s)",
    )
    parser.add_argument(
        "--format",
        default="png",
        choices=["png", "svg", "pdf"],
        help="Output format (default: %(default)s)",
    )
    parser.add_argument(
        "--param-sets",
        default="",
        help="Comma-separated param sets to plot (e.g., 44,65,87). Default: all",
    )
    return parser.parse_args()


def main():
    args = parse_args()

    try:
        import matplotlib.pyplot as plt
    except ImportError as exc:
        print("matplotlib is required to generate plots", file=sys.stderr)
        print(f"ImportError: {exc}", file=sys.stderr)
        return 2

    data = load_kappa_counts(args.kappa_csv)
    if not data:
        print(f"No data found in {args.kappa_csv}", file=sys.stderr)
        return 1

    if args.param_sets:
        keep = {p.strip() for p in args.param_sets.split(",") if p.strip()}
        data = {k: v for k, v in data.items() if k in keep}
        if not data:
            print("No matching param sets after filtering", file=sys.stderr)
            return 1

    os.makedirs(args.out_dir, exist_ok=True)
    buckets = kappa_buckets()
    x = list(range(len(buckets)))
    bar_w = 0.4

    for param_set, modes in sorted(data.items(), key=lambda x: int(x[0])):
        baseline = modes.get("baseline", {})
        channel = modes.get("channel", {})
        base_probs, base_total = counts_to_probs(baseline)
        chan_probs, chan_total = counts_to_probs(channel)
        if base_total == 0 or chan_total == 0:
            print(f"Skipping param set {param_set}: empty counts", file=sys.stderr)
            continue

        base_cdf = cdf_from_probs(base_probs)
        chan_cdf = cdf_from_probs(chan_probs)
        ks_d = ks_from_cdf(base_cdf, chan_cdf)
        print(
            f"param_set={param_set} ks_d={ks_d:.6f} "
            f"baseline_n={base_total} channel_n={chan_total}"
        )

        fig, axes = plt.subplots(2, 1, figsize=(8.5, 6.5), constrained_layout=True)

        ax = axes[0]
        ax.bar([i - bar_w / 2 for i in x], base_probs, width=bar_w, label="baseline")
        ax.bar([i + bar_w / 2 for i in x], chan_probs, width=bar_w, label="channel")
        ax.set_title(
            f"ML-DSA-{param_set} kappa distribution (1..15 exact, >=16 bucketed)"
        )
        ax.set_xlabel("kappa bucket")
        ax.set_ylabel("probability")
        ax.set_xticks(x)
        ax.set_xticklabels(buckets, rotation=0)
        ax.legend(loc="upper right")

        ax = axes[1]
        ax.step(x, base_cdf, where="post", label="baseline")
        ax.step(x, chan_cdf, where="post", label="channel")
        ax.set_title(f"Empirical CDF (KS D = {ks_d:.4f}; tail>=16 bucketed)")
        ax.set_xlabel("kappa bucket")
        ax.set_ylabel("CDF")
        ax.set_xticks(x)
        ax.set_xticklabels(buckets, rotation=0)
        ax.set_ylim(0.0, 1.0)
        ax.legend(loc="lower right")

        out_path = os.path.join(
            args.out_dir, f"kappa_cdf_mldsa{param_set}.{args.format}"
        )
        fig.savefig(out_path)
        plt.close(fig)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
