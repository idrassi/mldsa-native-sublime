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
            "Overlay kappa CDFs for two datasets (e.g., 20k vs 100k) per param set."
        )
    )
    parser.add_argument(
        "--kappa-csv-a",
        default="test/results/sc/kappa_counts_opt1_20k.csv",
        help="Path to first kappa_counts CSV (default: %(default)s)",
    )
    parser.add_argument(
        "--kappa-csv-b",
        default="test/results/sc/kappa_counts_opt1_100k.csv",
        help="Path to second kappa_counts CSV (default: %(default)s)",
    )
    parser.add_argument(
        "--label-a",
        default="20k",
        help="Label for first dataset (default: %(default)s)",
    )
    parser.add_argument(
        "--label-b",
        default="100k",
        help="Label for second dataset (default: %(default)s)",
    )
    parser.add_argument(
        "--out-dir",
        default="test/results/sc/plots_overlay",
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

    data_a = load_kappa_counts(args.kappa_csv_a)
    data_b = load_kappa_counts(args.kappa_csv_b)
    if not data_a or not data_b:
        print("One or both kappa CSV inputs are empty", file=sys.stderr)
        return 1

    if args.param_sets:
        keep = {p.strip() for p in args.param_sets.split(",") if p.strip()}
        data_a = {k: v for k, v in data_a.items() if k in keep}
        data_b = {k: v for k, v in data_b.items() if k in keep}
        if not data_a or not data_b:
            print("No matching param sets after filtering", file=sys.stderr)
            return 1

    os.makedirs(args.out_dir, exist_ok=True)
    buckets = kappa_buckets()
    x = list(range(len(buckets)))

    for param_set in sorted(set(data_a.keys()) & set(data_b.keys()), key=int):
        modes_a = data_a.get(param_set, {})
        modes_b = data_b.get(param_set, {})

        base_a, _ = counts_to_probs(modes_a.get("baseline", {}))
        base_b, _ = counts_to_probs(modes_b.get("baseline", {}))
        chan_a, _ = counts_to_probs(modes_a.get("channel", {}))
        chan_b, _ = counts_to_probs(modes_b.get("channel", {}))

        base_cdf_a = cdf_from_probs(base_a)
        base_cdf_b = cdf_from_probs(base_b)
        chan_cdf_a = cdf_from_probs(chan_a)
        chan_cdf_b = cdf_from_probs(chan_b)

        ks_base = ks_from_cdf(base_cdf_a, base_cdf_b)
        ks_chan = ks_from_cdf(chan_cdf_a, chan_cdf_b)
        print(
            f"param_set={param_set} ks_base={ks_base:.6f} ks_channel={ks_chan:.6f}"
        )

        fig, axes = plt.subplots(2, 1, figsize=(8.5, 6.0), constrained_layout=True)

        ax = axes[0]
        ax.step(x, base_cdf_a, where="post", label=f"baseline {args.label_a}")
        ax.step(x, base_cdf_b, where="post", label=f"baseline {args.label_b}")
        ax.set_title(
            f"ML-DSA-{param_set} baseline CDF "
            f"(KS D = {ks_base:.4f}; tail>=16 bucketed)"
        )
        ax.set_xlabel("kappa bucket")
        ax.set_ylabel("CDF")
        ax.set_xticks(x)
        ax.set_xticklabels(buckets, rotation=0)
        ax.set_ylim(0.0, 1.0)
        ax.legend(loc="lower right")

        ax = axes[1]
        ax.step(x, chan_cdf_a, where="post", label=f"channel {args.label_a}")
        ax.step(x, chan_cdf_b, where="post", label=f"channel {args.label_b}")
        ax.set_title(
            f"ML-DSA-{param_set} channel CDF "
            f"(KS D = {ks_chan:.4f}; tail>=16 bucketed)"
        )
        ax.set_xlabel("kappa bucket")
        ax.set_ylabel("CDF")
        ax.set_xticks(x)
        ax.set_xticklabels(buckets, rotation=0)
        ax.set_ylim(0.0, 1.0)
        ax.legend(loc="lower right")

        out_path = os.path.join(
            args.out_dir, f"kappa_cdf_overlay_mldsa{param_set}.{args.format}"
        )
        fig.savefig(out_path)
        plt.close(fig)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
