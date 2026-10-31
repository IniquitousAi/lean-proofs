# release-subb: circuit-lane formalizations (Lean 4 + Mathlib)

A machine-checked formalization of known results (Subbotovskaya 1961, Andreev 1987,
Khrapchenko 1971), not new math, not P vs NP.

Check: `PKGS=<existing .lake/packages for this Mathlib rev> ./check.sh` (no new Mathlib download),
or `./check.sh` (runs `lake exe cache get`). Result of our run: check_run.log.
All theorems below: 0 sorry, axioms propext, Classical.choice, Quot.sound only [checked].

Formula model: De Morgan formulas (literals, binary AND/OR), size = number of leaves.

| Theorem (file) | Statement | Prior art |
|---|---|---|
| subbotovskaya_shrinkage, parity_formula_lb_full (Subbotovskaya, SubbotovskayaRandom) | fixing one variable of a Nice formula on m vars gives L' <= (1 - 3/(2m)) L (Nice is satisfiable; minimal formulas are Nice); L(XOR_m)^2 >= m^3 | Subbotovskaya 1961 |
| subbotovskaya_random (SubbotovskayaRandom) | E[L] <= ((m-j)/m)^1.5 L + 1 after j random fixings | Subbotovskaya; +1 form as in Rossman's notes, Cor 12 |
| subbotovskaya_Rp, Ep_eq_Ptrue, subbotovskaya_Rp_true (SubbotovskayaRp, RpTrue) | true independent R_p: E[L] <= p sqrt(p+(1-p)/m) L + 1 | standard textbook form |
| andreev_reduction, exists_hard, andreev_lower_bound (Andreev, AndreevFinal) | explicit Andreev function on n = 2^r + r 2^r bits: (2^r-2)/(4r) - 1 <= (r/2^r)^1.5 L (left side is negative at r = 4, so the bound is empty there and meaningful for r >= 5) | Andreev 1987 (exponent 2.5 version) |
| khrapchenko, parity_khrapchenko (Khrapchenko) | e(A,B)^2 <= L |A||B|; L(XOR_n) >= n^2 | Khrapchenko 1971; already formalized in complexitylib, ours is an independent proof on our formula type |
| parity_upper, parity_tight (ParityUpper) | L(XOR_{2^k}) = 4^k exactly | classical |
| decomposition, piece_bound (Decomp) | greedy split into <= L/l pieces of size in [l,2l); per-piece E[L] <= mp + C(m,2)p^2 L | step 1 and partial step 2 of Hastad/Tal plan |

Labels:
- [reasoned] andreev_lower_bound gives L >= n^2.5 / polylog n, i.e. n^(2.5-o(1)).
- [reasoned] parity_tight shows the shrinkage exponent is at most 2. Hastad's matching lower
  bound (exponent 2, giving Andreev n^(3-o(1))) is NOT formalized.
- [checked] decomposition counts leaf mass only; pieces with at most 2 holes (Tal's interface)
  are not yet formalized.
