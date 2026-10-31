# HHH: unconditional MOD_q ∉ AC0[p] bounds in Lean 4

Lean files that sit on top of the Berkeley CS294-268 project
"AC0[2] Circuit Lower Bounds" (Yichuan Wang), pinned to
github.com/ucb-lean-course-sp26/final-projects @ fbb5be4875dd86fd0e180b97e359a6cece930cbd.
No upstream file is modified. No sorry (the one grep hit in HHH_Repair.lean is the word inside a comment). Axioms: propext, Classical.choice, Quot.sound.

## Run
    # PKGS=/existing/.lake/packages ./check.sh reuses an existing Mathlib (no new copy)
    ./check.sh        # clones upstream at the pinned commit, overlays Project/HHH_*.lean,
                      # fetches the Mathlib cache, builds, prints axioms
Needs elan (Lean toolchain from lean-toolchain: v4.30.0-rc1), git, network.
lake-manifest.json pins Mathlib and the other dependencies.

## Files
- HHH_Vacuity.lean: the upstream quantitative theorem forces δ = 0 (δ : ℕ).
- HHH_Repair.lean: fractional restatement MODq_notin_AC0p_fractional; counting helpers.
- HHH_Asymptotic.lean: central-binomial tail bound, explicit bound for even n.
- HHH_Final.lean: every n; MODq_AC0p_size_ge (size ≥ 2^ellStarN / (2^q·8q(n+1)(n+2)) for n ≥ 16q+32);
  ellStarN_closed_form.
- HHH_Real.lean: MODq_AC0p_rpow: for depth d ≥ 1,
  2^(c·n^(1/(2d))) ≤ 2·2^q·8q(n+1)(n+2)·size, c = 1/((p-1)·64^(1/(2d))), n ≥ 16q+32.
- HHH_Sanity.lean: an explicit 1-gate AC0[3] circuit computing MOD_2 (model is not empty).

Inputs are n + (q-1) bits (the upstream padded MOD_q), and size counts non-input gates.
This is an AC0[p] lower bound only. It says nothing about P vs NP.
