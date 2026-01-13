#!/usr/bin/env python3
import argparse
import csv
import os
import sys


def load_reject_rates(path):
    data = {}
    with open(path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            param_set = row.get("param_set")
            mode = row.get("mode")
            if not param_set or not mode:
                continue
            data.setdefault(param_set, {})[mode] = row
    return data


def load_kappa_summary(path):
    data = {}
    with open(path, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            param_set = row.get("param_set")
            mode = row.get("mode")
            if not param_set or not mode:
                continue
            data.setdefault(param_set, {})[mode] = row
    return data


def parse_args():
    parser = argparse.ArgumentParser(
        description="Plot extra SC stats (reject rates, kappa tail, mean CI)."
    )
    parser.add_argument(
        "--reject-csv",
        required=True,
        help="Path to reject_rates CSV (from sc_extra_stats.py)",
    )
    parser.add_argument(
        "--kappa-csv",
        required=True,
        help="Path to kappa_summary CSV (from sc_extra_stats.py)",
    )
    parser.add_argument(
        "--out-dir",
        default="test/results/sc/plots_extra",
        help="Output directory (default: %(default)s)",
    )
    parser.add_argument(
        "--format",
        default="png",
        choices=["png", "svg", "pdf"],
        help="Output format (default: %(default)s)",
    )
    parser.add_argument(
        "--tag",
        default="opt1_100k",
        help="Tag for output filenames (default: %(default)s)",
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

    rejects = load_reject_rates(args.reject_csv)
    kappa = load_kappa_summary(args.kappa_csv)
    if not rejects or not kappa:
        print("Reject or kappa CSV data is empty", file=sys.stderr)
        return 1

    if args.param_sets:
        keep = {p.strip() for p in args.param_sets.split(",") if p.strip()}
        rejects = {k: v for k, v in rejects.items() if k in keep}
        kappa = {k: v for k, v in kappa.items() if k in keep}
        if not rejects or not kappa:
            print("No matching param sets after filtering", file=sys.stderr)
            return 1

    os.makedirs(args.out_dir, exist_ok=True)
    param_sets = sorted(set(rejects.keys()) & set(kappa.keys()), key=int)
    if not param_sets:
        print("No overlapping param sets between inputs", file=sys.stderr)
        return 1

    # Plot 1: reject rates per attempt by reason.
    reasons = [
        ("reject_z_rate", "z"),
        ("reject_w0_rate", "w0"),
        ("reject_h_rate", "h"),
        ("reject_hint_rate", "hint"),
    ]
    fig, axes = plt.subplots(
        len(param_sets), 1, figsize=(8.5, 2.8 * len(param_sets)), constrained_layout=True
    )
    if len(param_sets) == 1:
        axes = [axes]
    bar_w = 0.35
    x = list(range(len(reasons)))
    for ax, param_set in zip(axes, param_sets):
        base = rejects[param_set].get("baseline", {})
        chan = rejects[param_set].get("channel", {})
        base_vals = [float(base.get(key, 0.0)) * 100.0 for key, _ in reasons]
        chan_vals = [float(chan.get(key, 0.0)) * 100.0 for key, _ in reasons]
        ax.bar([i - bar_w / 2 for i in x], base_vals, width=bar_w, label="baseline")
        ax.bar([i + bar_w / 2 for i in x], chan_vals, width=bar_w, label="channel")
        ax.set_title(f"ML-DSA-{param_set} reject rates per attempt")
        ax.set_ylabel("rate (%)")
        ax.set_xticks(x)
        ax.set_xticklabels([label for _, label in reasons])
        if ax is axes[0]:
            ax.legend(loc="upper right")
    out_path = os.path.join(
        args.out_dir, f"reject_rates_{args.tag}.{args.format}"
    )
    fig.savefig(out_path)
    plt.close(fig)

    # Plot 2: tail probability P(kappa>=16).
    fig, ax = plt.subplots(figsize=(8.0, 4.5), constrained_layout=True)
    base_tail = []
    chan_tail = []
    for param_set in param_sets:
        base_tail.append(float(kappa[param_set]["baseline"]["tail_prob"]) * 100.0)
        chan_tail.append(float(kappa[param_set]["channel"]["tail_prob"]) * 100.0)
    x = list(range(len(param_sets)))
    ax.bar([i - bar_w / 2 for i in x], base_tail, width=bar_w, label="baseline")
    ax.bar([i + bar_w / 2 for i in x], chan_tail, width=bar_w, label="channel")
    ax.set_title("Tail probability P(kappa>=16)")
    ax.set_ylabel("probability (%)")
    ax.set_xticks(x)
    ax.set_xticklabels([f"ML-DSA-{p}" for p in param_sets])
    ax.legend(loc="upper right")
    out_path = os.path.join(
        args.out_dir, f"kappa_tail_{args.tag}.{args.format}"
    )
    fig.savefig(out_path)
    plt.close(fig)

    # Plot 3: mean attempts with 95% CI (approx from hist).
    fig, ax = plt.subplots(figsize=(8.0, 4.5), constrained_layout=True)
    x = list(range(len(param_sets)))
    offset = 0.12
    base_means = []
    chan_means = []
    base_err = []
    chan_err = []
    for param_set in param_sets:
        base = kappa[param_set]["baseline"]
        chan = kappa[param_set]["channel"]
        nstat = float(base["nstat"])
        base_mean = float(base["mean_attempts"])
        chan_mean = float(chan["mean_attempts"])
        base_var = float(base["var_from_hist"])
        chan_var = float(chan["var_from_hist"])
        base_se = (base_var / nstat) ** 0.5 if nstat > 0 else 0.0
        chan_se = (chan_var / nstat) ** 0.5 if nstat > 0 else 0.0
        base_means.append(base_mean)
        chan_means.append(chan_mean)
        base_err.append(1.96 * base_se)
        chan_err.append(1.96 * chan_se)
    ax.errorbar(
        [i - offset for i in x],
        base_means,
        yerr=base_err,
        fmt="o",
        label="baseline",
        capsize=4,
    )
    ax.errorbar(
        [i + offset for i in x],
        chan_means,
        yerr=chan_err,
        fmt="o",
        label="channel",
        capsize=4,
    )
    ax.set_title("Mean attempts with 95% CI (tail>=16->16)")
    ax.set_ylabel("mean attempts")
    ax.set_xticks(x)
    ax.set_xticklabels([f"ML-DSA-{p}" for p in param_sets])
    ax.legend(loc="upper right")
    out_path = os.path.join(args.out_dir, f"mean_ci_{args.tag}.{args.format}")
    fig.savefig(out_path)
    plt.close(fig)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
