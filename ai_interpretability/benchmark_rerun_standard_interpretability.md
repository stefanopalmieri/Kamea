# Benchmark Rerun: Standard Interpretability Methods on L_role-Regularized Networks

## Goal

Rerun the interpretability benchmark (DS Recovery, K-Means, Linear Probe, Activation Patching) on networks trained with L_role regularization. Compare against the baseline benchmark results. Test whether axiom-derived regularization makes standard tools work better.

## Setup

Use the same benchmark code from the previous benchmark experiment. The only change is the training regime: train networks with `L = L_task + 0.5 * L_role` instead of `L = L_task`. Use the same H=128 architecture, same number of trials (10), same evaluation metrics (ARI for role recovery).

Run on both Δ₁ and the control algebra, same as before.

## Expected Results

Baseline benchmark results were:
- DS Recovery: ARI = 1.00 (Δ₁), 0.00 (Control)
- K-Means: ARI = 0.18 (Δ₁), -0.03 (Control)
- Linear Probe: ARI = 0.23 (Δ₁), -0.03 (Control)
- Activation Patching: ARI = -0.005 (Δ₁), -0.005 (Control)

We predict L_role will dramatically improve K-Means and Linear Probe on Δ₁ while leaving Control scores unchanged.

## Output

1. `regularized_benchmark.png` — Side-by-side bar chart: baseline-trained vs role_only-trained, all 4 methods, both Δ₁ and Control. Same format as the original benchmark_results.png but with paired bars.

2. `regularized_benchmark_table.txt` — Summary table with all numbers.

3. `regularized_benchmark_detail.png` — K-Means confusion matrix for role_only network (compare against the baseline confusion matrix to see if clusters now align with roles).
