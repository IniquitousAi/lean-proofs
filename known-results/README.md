# Known results, machine-checked

Three Lean 4 developments of theorems that were already known on paper. Each folder is its own project with its own
pinned Lean and Mathlib versions (so they are not part of the main build), and its own `check.sh`: it builds the files,
counts `sorry` (0) and prints the axioms each main theorem rests on (only propext, Classical.choice, Quot.sound).

None of them is new mathematics, and none of them is about solving P vs NP.

## razborov-smolensky/

Label: a machine-checked formalization of the known 1987 Razborov-Smolensky theorem, not new math, not P vs NP.

Run: `cd razborov-smolensky && ./check.sh` (needs elan, git and network; it fetches Mathlib).

## algebrization/

Label: a machine-checked formalization of the known 2009 Aaronson-Wigderson algebrization barrier, not new math, not P vs NP.

Run: `cd algebrization && ./check.sh` (needs elan, git and network; it fetches Mathlib).

Receipt: `check_run.log` is a full run of `check.sh` (build OK, 0 sorry, standard axioms).

## formula-lower-bounds/

Label: a machine-checked formalization of known results (Subbotovskaya 1961, Khrapchenko 1971, Andreev 1987), not new math, not P vs NP.

Run: `cd formula-lower-bounds && ./check.sh` (needs elan, git and network; it fetches Mathlib).

Receipt: `check_run.log` is a full run of `check.sh` (build OK, 0 sorry, standard axioms).
