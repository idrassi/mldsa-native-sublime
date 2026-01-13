# Subliminal Channel Experiment Pipeline

End-to-end steps to regenerate the SC CSVs and plots consumed by the paper.

1) **Build with SC enabled** (randomized API must be available):
   ```sh
   make clean
   make OPT=1 EXTRA_CFLAGS="-DMLD_CONFIG_SC" test_sc
   ```
   The binaries live under `test/build/mldsaXX/bin/test_scXX`.

2) **Run workloads** (paper settings shown below) and capture logs:
   ```sh
   MLD_SC_NSIG=500 MLD_SC_NSTAT=100000 MLD_SC_NDIST=100000 \
     ./test/build/mldsa44/bin/test_sc44 | tee test/results/sc/sc44_opt1_100k.log
   MLD_SC_NSIG=500 MLD_SC_NSTAT=100000 MLD_SC_NDIST=100000 \
     ./test/build/mldsa65/bin/test_sc65 | tee test/results/sc/sc65_opt1_100k.log
   MLD_SC_NSIG=500 MLD_SC_NSTAT=100000 MLD_SC_NDIST=100000 \
     ./test/build/mldsa87/bin/test_sc87 | tee test/results/sc/sc87_opt1_100k.log
   ```
   (Use `MLD_SC_NSTAT=20000 MLD_SC_NDIST=20000` for 20k runs.) Logs contain
   `param_set=<44|65|87>` along with abort stats and histograms bucketed as
   κ=1..15 and a tail bin κ>=16.

3) **Convert logs to CSVs** (summary + kappa counts):
   ```sh
   python scripts/sc_collect_results.py \
     test/results/sc/sc44_opt1_100k.log \
     test/results/sc/sc65_opt1_100k.log \
     test/results/sc/sc87_opt1_100k.log \
     --tag opt1_100k --out-dir test/results/sc
   ```

4) **Compute extra stats (tail prob, CI, reject shares)**:
   ```sh
   python scripts/sc_extra_stats.py \
     --summary-csv test/results/sc/summary_opt1_100k.csv \
     --kappa-csv test/results/sc/kappa_counts_opt1_100k.csv \
     --tag opt1_100k --out-dir test/results/sc
   ```

5) **Plot**:
   ```sh
   python scripts/plot_sc_results.py \
     --kappa-csv test/results/sc/kappa_counts_opt1_100k.csv \
     --out-dir test/results/sc/plots_100k

   python scripts/plot_sc_overlay.py \
     --kappa-csv-a test/results/sc/kappa_counts_opt1_20k.csv \
     --kappa-csv-b test/results/sc/kappa_counts_opt1_100k.csv \
     --out-dir test/results/sc/plots_overlay

   python scripts/plot_sc_extra.py \
     --reject-csv test/results/sc/reject_rates_opt1_100k.csv \
     --kappa-csv test/results/sc/kappa_summary_opt1_100k.csv \
     --tag opt1_100k \
     --out-dir test/results/sc/plots_extra_100k
   ```

These steps recreate the CSVs consumed by `sc_extra_stats.py` and the plots
referenced in the paper. All κ plots use the bucketed histogram resolution
noted above.
