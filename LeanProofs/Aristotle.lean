import Mathlib

/-!
# The Proof Tower's yellow answer-bank blocks, for Aristotle

Each block of the tower is one theorem (`count_exact`, `key_oeis`, `graphs_agree`), built from one statement per item. Every item
is left as `sorry`. A proof is accepted only if it compiles, has no `sorry`, and `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound` (so no `native_decide`). Do not change the statements or the definitions.
-/

open Finset

namespace TowerBatch

/-- A card is 0 to 51; its rank is 1 (ace) to 13 (king), four cards each, as in the engine. -/
def rank (c : Fin 52) : ℕ := c.val / 4 + 1

/-- The first place (1-based) of a shuffled deck holding a card with property `p` (the deck holds one: `σ i` is the card at place `i + 1`). -/
def firstPlace {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin n → Prop) [DecidablePred p] : ℕ :=
  1 + (univ.filter (fun i : Fin n => ∀ j : Fin n, j ≤ i → ¬ p (σ j))).card

/-- The last place (1-based) of a shuffled deck holding a card with property `p`. -/
def lastPlace {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Fin n → Prop) [DecidablePred p] : ℕ :=
  n - (univ.filter (fun i : Fin n => ∀ j : Fin n, i ≤ j → ¬ p (σ j))).card

/-- How many of `n` coins (true = heads) came up heads. -/
def heads {n : ℕ} (x : Fin n → Bool) : ℕ := (univ.filter (fun i => x i = true)).card

/-- The chance of one row of coins, each heads with chance `q`. -/
def rowChance {n : ℕ} (q : ℚ) (x : Fin n → Bool) : ℚ := ∏ i, if x i then q else 1 - q

/-- One step on the square grid. -/
def dir : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- Where a walk of `n` steps stands after its first `k` steps. -/
def pos {n : ℕ} (s : Fin n → Fin 4) (k : Fin (n + 1)) : ℤ × ℤ := ∑ i : Fin n, if i.val < k.val then dir (s i) else 0

/-- The walks of `n` steps on the square grid that never visit a point twice. -/
def selfAvoiding (n : ℕ) : ℕ := (univ.filter (fun s : Fin n → Fin 4 => Function.Injective (pos s))).card

/-- Two vertices are joined in the edge list `E` (either way round). -/
def Adj (E : List (ℕ × ℕ)) (a b : ℕ) : Prop := (a, b) ∈ E ∨ (b, a) ∈ E

/-- No three vertices are all joined. -/
def TriangleFree (n : ℕ) (E : List (ℕ × ℕ)) : Prop :=
  ∀ a b c : Fin n, Adj E a b → Adj E b c → Adj E a c → False

/-- Every `k` vertices hold at least one joined pair (no `k` strangers). -/
def NoStrangers (n k : ℕ) (E : List (ℕ × ℕ)) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → ∃ a ∈ S, ∃ b ∈ S, Adj E a b

/-- amcs-n13-k5-2026-10-15T01-53-33-663Z.json: 13 vertices, 26 edges. -/
def graph_amcs_n13_k5_2026_10_15T01_53_33_663Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 4), (0, 6), (1, 8), (1, 9), (1, 10), (2, 7), (2, 8), (2, 12), (3, 4), (3, 6), (3, 8), (3, 9), (4, 7), (4, 11), (5, 6), (5, 7), (5, 9), (5, 11), (6, 10), (7, 10), (8, 11), (9, 12), (10, 12), (11, 12)]

/-- amcs-n13-k5-2026-10-15T01-54-36-788Z.json: 13 vertices, 26 edges. -/
def graph_amcs_n13_k5_2026_10_15T01_54_36_788Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 5), (0, 10), (1, 9), (1, 11), (1, 12), (2, 6), (2, 7), (2, 9), (3, 5), (3, 6), (3, 9), (3, 10), (4, 5), (4, 6), (4, 8), (4, 11), (5, 7), (6, 12), (7, 11), (7, 12), (8, 9), (8, 10), (8, 12), (10, 11)]

/-- amcs-n17-k6-2026-10-15T01-53-33-852Z.json: 17 vertices, 41 edges. -/
def graph_amcs_n17_k6_2026_10_15T01_53_33_852Z_edges : List (ℕ × ℕ) := [(0, 3), (0, 7), (0, 9), (0, 14), (0, 15), (1, 7), (1, 9), (1, 10), (1, 11), (1, 15), (2, 3), (2, 4), (2, 5), (2, 9), (2, 13), (3, 8), (3, 11), (3, 16), (4, 6), (4, 10), (4, 15), (5, 7), (5, 12), (5, 16), (6, 7), (6, 9), (6, 11), (6, 16), (7, 8), (8, 10), (8, 12), (8, 13), (9, 12), (10, 14), (10, 16), (11, 12), (11, 14), (12, 15), (13, 14), (13, 15), (13, 16)]

/-- amcs-n17-k6-2026-10-15T01-54-36-944Z.json: 17 vertices, 42 edges. -/
def graph_amcs_n17_k6_2026_10_15T01_54_36_944Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 7), (0, 9), (0, 13), (0, 16), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 7), (2, 11), (2, 16), (3, 8), (3, 12), (3, 13), (4, 9), (4, 14), (4, 15), (5, 7), (5, 8), (5, 10), (5, 11), (6, 8), (6, 11), (6, 12), (6, 15), (7, 14), (7, 15), (8, 9), (8, 16), (9, 11), (9, 12), (10, 12), (10, 15), (10, 16), (11, 13), (12, 14), (13, 14), (13, 15), (14, 16)]

/-- amcs-n22-k7-2026-10-15T01-54-54-955Z.json: 22 vertices, 65 edges. -/
def graph_amcs_n22_k7_2026_10_15T01_54_54_955Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 7), (0, 9), (0, 16), (1, 6), (1, 8), (1, 9), (1, 13), (1, 14), (1, 18), (2, 4), (2, 12), (2, 14), (2, 20), (2, 21), (3, 11), (3, 14), (3, 18), (3, 19), (3, 20), (4, 7), (4, 8), (4, 11), (4, 15), (4, 19), (5, 8), (5, 11), (5, 13), (5, 14), (5, 16), (5, 21), (6, 11), (6, 16), (6, 17), (6, 20), (6, 21), (7, 10), (7, 13), (7, 17), (7, 18), (8, 17), (8, 20), (9, 10), (9, 11), (9, 15), (9, 21), (10, 14), (10, 16), (10, 19), (10, 20), (11, 12), (12, 16), (12, 17), (12, 18), (12, 19), (13, 15), (13, 19), (13, 20), (14, 17), (15, 16), (15, 17), (15, 18), (18, 21), (19, 21)]

/-- amcs-n8-k4-2026-10-15T01-53-33-552Z.json: 8 vertices, 12 edges. -/
def graph_amcs_n8_k4_2026_10_15T01_53_33_552Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 5), (1, 2), (1, 3), (2, 6), (2, 7), (3, 4), (3, 7), (4, 6), (5, 6), (5, 7)]

/-- amcs-n8-k4-2026-10-15T01-54-36-642Z.json: 8 vertices, 11 edges. -/
def graph_amcs_n8_k4_2026_10_15T01_54_36_642Z_edges : List (ℕ × ℕ) := [(0, 3), (0, 4), (0, 6), (1, 2), (1, 4), (2, 6), (2, 7), (3, 7), (4, 5), (5, 6), (5, 7)]

/-- anneal-n13-k5-2026-10-14T13-56-23-903Z.json: 13 vertices, 26 edges. -/
def graph_anneal_n13_k5_2026_10_14T13_56_23_903Z_edges : List (ℕ × ℕ) := [(0, 4), (0, 5), (0, 7), (0, 11), (1, 5), (1, 6), (1, 8), (1, 11), (2, 3), (2, 5), (2, 6), (2, 12), (3, 7), (3, 9), (3, 11), (4, 6), (4, 8), (4, 9), (5, 9), (6, 10), (7, 8), (7, 10), (8, 12), (9, 10), (10, 12), (11, 12)]

/-- anneal-n13-k5-2026-10-14T14-06-17-873Z.json: 13 vertices, 26 edges. -/
def graph_anneal_n13_k5_2026_10_14T14_06_17_873Z_edges : List (ℕ × ℕ) := [(0, 4), (0, 5), (0, 7), (0, 11), (1, 5), (1, 6), (1, 8), (1, 11), (2, 3), (2, 5), (2, 6), (2, 12), (3, 7), (3, 9), (3, 11), (4, 6), (4, 8), (4, 9), (5, 9), (6, 10), (7, 8), (7, 10), (8, 12), (9, 10), (10, 12), (11, 12)]

/-- anneal-n13-k5-2026-10-14T15-10-04-875Z.json: 13 vertices, 26 edges. -/
def graph_anneal_n13_k5_2026_10_14T15_10_04_875Z_edges : List (ℕ × ℕ) := [(0, 4), (0, 5), (0, 7), (0, 11), (1, 5), (1, 6), (1, 8), (1, 11), (2, 3), (2, 5), (2, 6), (2, 12), (3, 7), (3, 9), (3, 11), (4, 6), (4, 8), (4, 9), (5, 9), (6, 10), (7, 8), (7, 10), (8, 12), (9, 10), (10, 12), (11, 12)]

/-- anneal-n13-k5-2026-10-14T15-11-12-007Z.json: 13 vertices, 26 edges. -/
def graph_anneal_n13_k5_2026_10_14T15_11_12_007Z_edges : List (ℕ × ℕ) := [(0, 4), (0, 5), (0, 7), (0, 11), (1, 5), (1, 6), (1, 8), (1, 11), (2, 3), (2, 5), (2, 6), (2, 12), (3, 7), (3, 9), (3, 11), (4, 6), (4, 8), (4, 9), (5, 9), (6, 10), (7, 8), (7, 10), (8, 12), (9, 10), (10, 12), (11, 12)]

/-- anneal-n13-k5-2026-10-14T15-23-48-940Z.json: 13 vertices, 26 edges. -/
def graph_anneal_n13_k5_2026_10_14T15_23_48_940Z_edges : List (ℕ × ℕ) := [(0, 4), (0, 5), (0, 7), (0, 11), (1, 5), (1, 6), (1, 8), (1, 11), (2, 3), (2, 5), (2, 6), (2, 12), (3, 7), (3, 9), (3, 11), (4, 6), (4, 8), (4, 9), (5, 9), (6, 10), (7, 8), (7, 10), (8, 12), (9, 10), (10, 12), (11, 12)]

/-- circulant-n13-k5-2026-10-14T13-56-23-520Z.json: 13 vertices, 26 edges. -/
def graph_circulant_n13_k5_2026_10_14T13_56_23_520Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 10), (0, 11), (1, 3), (1, 4), (1, 11), (1, 12), (2, 4), (2, 5), (2, 12), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11), (9, 12), (10, 12)]

/-- circulant-n13-k5-2026-10-14T14-06-20-071Z.json: 13 vertices, 26 edges. -/
def graph_circulant_n13_k5_2026_10_14T14_06_20_071Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 10), (0, 11), (1, 3), (1, 4), (1, 11), (1, 12), (2, 4), (2, 5), (2, 12), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11), (9, 12), (10, 12)]

/-- circulant-n13-k5-2026-10-14T15-10-07-045Z.json: 13 vertices, 26 edges. -/
def graph_circulant_n13_k5_2026_10_14T15_10_07_045Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 10), (0, 11), (1, 3), (1, 4), (1, 11), (1, 12), (2, 4), (2, 5), (2, 12), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11), (9, 12), (10, 12)]

/-- circulant-n13-k5-2026-10-14T15-11-14-178Z.json: 13 vertices, 26 edges. -/
def graph_circulant_n13_k5_2026_10_14T15_11_14_178Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 10), (0, 11), (1, 3), (1, 4), (1, 11), (1, 12), (2, 4), (2, 5), (2, 12), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11), (9, 12), (10, 12)]

/-- circulant-n13-k5-2026-10-14T15-23-51-122Z.json: 13 vertices, 26 edges. -/
def graph_circulant_n13_k5_2026_10_14T15_23_51_122Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 10), (0, 11), (1, 3), (1, 4), (1, 11), (1, 12), (2, 4), (2, 5), (2, 12), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11), (9, 12), (10, 12)]

/-- circulant-n35-k9-2026-10-14T13-56-47-249Z.json: 35 vertices, 140 edges. -/
def graph_circulant_n35_k9_2026_10_14T13_56_47_249Z_edges : List (ℕ × ℕ) := [(0, 4), (0, 6), (0, 7), (0, 9), (0, 26), (0, 28), (0, 29), (0, 31), (1, 5), (1, 7), (1, 8), (1, 10), (1, 27), (1, 29), (1, 30), (1, 32), (2, 6), (2, 8), (2, 9), (2, 11), (2, 28), (2, 30), (2, 31), (2, 33), (3, 7), (3, 9), (3, 10), (3, 12), (3, 29), (3, 31), (3, 32), (3, 34), (4, 8), (4, 10), (4, 11), (4, 13), (4, 30), (4, 32), (4, 33), (5, 9), (5, 11), (5, 12), (5, 14), (5, 31), (5, 33), (5, 34), (6, 10), (6, 12), (6, 13), (6, 15), (6, 32), (6, 34), (7, 11), (7, 13), (7, 14), (7, 16), (7, 33), (8, 12), (8, 14), (8, 15), (8, 17), (8, 34), (9, 13), (9, 15), (9, 16), (9, 18), (10, 14), (10, 16), (10, 17), (10, 19), (11, 15), (11, 17), (11, 18), (11, 20), (12, 16), (12, 18), (12, 19), (12, 21), (13, 17), (13, 19), (13, 20), (13, 22), (14, 18), (14, 20), (14, 21), (14, 23), (15, 19), (15, 21), (15, 22), (15, 24), (16, 20), (16, 22), (16, 23), (16, 25), (17, 21), (17, 23), (17, 24), (17, 26), (18, 22), (18, 24), (18, 25), (18, 27), (19, 23), (19, 25), (19, 26), (19, 28), (20, 24), (20, 26), (20, 27), (20, 29), (21, 25), (21, 27), (21, 28), (21, 30), (22, 26), (22, 28), (22, 29), (22, 31), (23, 27), (23, 29), (23, 30), (23, 32), (24, 28), (24, 30), (24, 31), (24, 33), (25, 29), (25, 31), (25, 32), (25, 34), (26, 30), (26, 32), (26, 33), (27, 31), (27, 33), (27, 34), (28, 32), (28, 34), (29, 33), (30, 34)]

/-- circulant-n38-k10-2026-10-14T13-56-49-410Z.json: 38 vertices, 171 edges. -/
def graph_circulant_n38_k10_2026_10_14T13_56_49_410Z_edges : List (ℕ × ℕ) := [(0, 6), (0, 7), (0, 9), (0, 11), (0, 19), (0, 27), (0, 29), (0, 31), (0, 32), (1, 7), (1, 8), (1, 10), (1, 12), (1, 20), (1, 28), (1, 30), (1, 32), (1, 33), (2, 8), (2, 9), (2, 11), (2, 13), (2, 21), (2, 29), (2, 31), (2, 33), (2, 34), (3, 9), (3, 10), (3, 12), (3, 14), (3, 22), (3, 30), (3, 32), (3, 34), (3, 35), (4, 10), (4, 11), (4, 13), (4, 15), (4, 23), (4, 31), (4, 33), (4, 35), (4, 36), (5, 11), (5, 12), (5, 14), (5, 16), (5, 24), (5, 32), (5, 34), (5, 36), (5, 37), (6, 12), (6, 13), (6, 15), (6, 17), (6, 25), (6, 33), (6, 35), (6, 37), (7, 13), (7, 14), (7, 16), (7, 18), (7, 26), (7, 34), (7, 36), (8, 14), (8, 15), (8, 17), (8, 19), (8, 27), (8, 35), (8, 37), (9, 15), (9, 16), (9, 18), (9, 20), (9, 28), (9, 36), (10, 16), (10, 17), (10, 19), (10, 21), (10, 29), (10, 37), (11, 17), (11, 18), (11, 20), (11, 22), (11, 30), (12, 18), (12, 19), (12, 21), (12, 23), (12, 31), (13, 19), (13, 20), (13, 22), (13, 24), (13, 32), (14, 20), (14, 21), (14, 23), (14, 25), (14, 33), (15, 21), (15, 22), (15, 24), (15, 26), (15, 34), (16, 22), (16, 23), (16, 25), (16, 27), (16, 35), (17, 23), (17, 24), (17, 26), (17, 28), (17, 36), (18, 24), (18, 25), (18, 27), (18, 29), (18, 37), (19, 25), (19, 26), (19, 28), (19, 30), (20, 26), (20, 27), (20, 29), (20, 31), (21, 27), (21, 28), (21, 30), (21, 32), (22, 28), (22, 29), (22, 31), (22, 33), (23, 29), (23, 30), (23, 32), (23, 34), (24, 30), (24, 31), (24, 33), (24, 35), (25, 31), (25, 32), (25, 34), (25, 36), (26, 32), (26, 33), (26, 35), (26, 37), (27, 33), (27, 34), (27, 36), (28, 34), (28, 35), (28, 37), (29, 35), (29, 36), (30, 36), (30, 37), (31, 37)]

/-- circulant-n8-k4-2026-10-14T13-56-23-372Z.json: 8 vertices, 12 edges. -/
def graph_circulant_n8_k4_2026_10_14T13_56_23_372Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 7), (1, 2), (1, 5), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (5, 6), (6, 7)]

/-- circulant-n8-k4-2026-10-14T14-06-20-015Z.json: 8 vertices, 12 edges. -/
def graph_circulant_n8_k4_2026_10_14T14_06_20_015Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 7), (1, 2), (1, 5), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (5, 6), (6, 7)]

/-- circulant-n8-k4-2026-10-14T15-10-06-995Z.json: 8 vertices, 12 edges. -/
def graph_circulant_n8_k4_2026_10_14T15_10_06_995Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 7), (1, 2), (1, 5), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (5, 6), (6, 7)]

/-- circulant-n8-k4-2026-10-14T15-11-14-131Z.json: 8 vertices, 12 edges. -/
def graph_circulant_n8_k4_2026_10_14T15_11_14_131Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 7), (1, 2), (1, 5), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (5, 6), (6, 7)]

/-- circulant-n8-k4-2026-10-14T15-23-51-067Z.json: 8 vertices, 12 edges. -/
def graph_circulant_n8_k4_2026_10_14T15_23_51_067Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 7), (1, 2), (1, 5), (2, 3), (2, 6), (3, 4), (3, 7), (4, 5), (5, 6), (6, 7)]

/-- exoo-n39-k10.json: 39 vertices, 167 edges. -/
def graph_exoo_n39_k10_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 6), (0, 10), (0, 15), (0, 23), (0, 26), (0, 33), (1, 2), (1, 7), (1, 11), (1, 16), (1, 24), (1, 27), (1, 34), (2, 3), (2, 8), (2, 12), (2, 17), (2, 20), (2, 28), (2, 30), (2, 37), (3, 4), (3, 9), (3, 13), (3, 18), (3, 21), (3, 29), (3, 31), (4, 5), (4, 14), (4, 19), (4, 25), (4, 32), (4, 36), (4, 38), (5, 6), (5, 9), (5, 12), (5, 17), (5, 21), (5, 29), (5, 34), (6, 7), (6, 13), (6, 18), (6, 22), (6, 25), (6, 30), (6, 36), (7, 8), (7, 14), (7, 19), (7, 23), (7, 26), (7, 31), (8, 9), (8, 10), (8, 15), (8, 24), (8, 27), (8, 32), (8, 38), (9, 11), (9, 16), (9, 20), (9, 28), (9, 33), (9, 37), (10, 11), (10, 14), (10, 19), (10, 22), (10, 29), (10, 31), (10, 36), (11, 12), (11, 15), (11, 23), (11, 25), (11, 32), (12, 13), (12, 16), (12, 24), (12, 26), (12, 33), (12, 38), (13, 14), (13, 17), (13, 20), (13, 27), (13, 34), (13, 37), (14, 18), (14, 21), (14, 28), (14, 30), (15, 16), (15, 19), (15, 21), (15, 28), (15, 34), (16, 17), (16, 22), (16, 29), (16, 30), (16, 36), (17, 18), (17, 23), (17, 25), (17, 31), (18, 19), (18, 24), (18, 26), (18, 32), (18, 38), (19, 20), (19, 27), (19, 33), (20, 21), (20, 24), (20, 26), (20, 32), (20, 38), (21, 22), (21, 27), (21, 33), (21, 36), (22, 23), (22, 28), (22, 34), (22, 37), (22, 38), (23, 24), (23, 29), (23, 30), (23, 36), (24, 25), (24, 31), (24, 37), (25, 26), (25, 29), (25, 33), (26, 27), (26, 34), (26, 37), (27, 28), (27, 30), (27, 35), (28, 29), (28, 31), (28, 36), (29, 32), (29, 35), (30, 31), (30, 34), (30, 38), (31, 32), (32, 33), (32, 37), (33, 34), (33, 35), (34, 36), (35, 36), (35, 37), (35, 38)]

/-- grown-n13-k5-1791990648209.json: 13 vertices, 26 edges. -/
def graph_grown_n13_k5_1791990648209_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 10), (0, 11), (1, 3), (1, 4), (1, 11), (1, 12), (2, 4), (2, 5), (2, 12), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11), (9, 12), (10, 12)]

/-- grown-n36-k10-1791990649104.json: 36 vertices, 147 edges. -/
def graph_grown_n36_k10_1791990649104_edges : List (ℕ × ℕ) := [(0, 9), (0, 18), (0, 22), (0, 23), (0, 25), (0, 27), (0, 32), (0, 35), (1, 7), (1, 11), (1, 21), (1, 23), (1, 26), (1, 31), (1, 32), (2, 5), (2, 10), (2, 15), (2, 25), (2, 27), (2, 28), (2, 29), (2, 31), (2, 35), (3, 7), (3, 10), (3, 11), (3, 20), (3, 22), (3, 29), (3, 34), (4, 6), (4, 8), (4, 9), (4, 10), (4, 12), (4, 32), (4, 35), (5, 6), (5, 7), (5, 12), (5, 17), (5, 19), (5, 26), (5, 32), (6, 14), (6, 23), (6, 24), (6, 29), (6, 31), (7, 8), (7, 9), (7, 18), (7, 25), (7, 33), (7, 35), (8, 16), (8, 20), (8, 21), (8, 23), (8, 27), (8, 29), (9, 17), (9, 19), (9, 24), (9, 26), (9, 28), (9, 29), (10, 14), (10, 17), (10, 18), (10, 23), (10, 30), (11, 12), (11, 15), (11, 17), (11, 27), (11, 30), (11, 35), (12, 13), (12, 18), (12, 22), (12, 23), (12, 25), (12, 28), (13, 17), (13, 19), (13, 24), (13, 29), (13, 34), (13, 35), (14, 15), (14, 16), (14, 19), (14, 25), (14, 26), (14, 27), (15, 18), (15, 22), (15, 23), (15, 24), (15, 34), (16, 17), (16, 24), (16, 28), (16, 31), (16, 32), (16, 35), (17, 21), (17, 25), (17, 33), (18, 20), (18, 21), (18, 29), (18, 31), (19, 20), (19, 21), (19, 30), (19, 31), (20, 24), (20, 25), (20, 26), (20, 33), (21, 22), (21, 24), (21, 28), (21, 35), (22, 26), (22, 31), (22, 33), (23, 33), (24, 27), (24, 30), (25, 30), (26, 34), (26, 35), (27, 33), (27, 34), (28, 33), (28, 34), (29, 30), (29, 32), (30, 33), (30, 34), (31, 34), (32, 33), (32, 34)]

/-- ladder-n13-k5-2026-10-14T13-57-09-399Z.json: 13 vertices, 26 edges. -/
def graph_ladder_n13_k5_2026_10_14T13_57_09_399Z_edges : List (ℕ × ℕ) := [(0, 3), (0, 4), (0, 9), (0, 11), (1, 2), (1, 3), (1, 10), (1, 11), (2, 6), (2, 8), (2, 9), (3, 5), (3, 12), (4, 6), (4, 10), (4, 12), (5, 6), (5, 8), (5, 10), (6, 7), (7, 9), (7, 11), (7, 12), (8, 11), (8, 12), (9, 10)]

/-- ladder-n17-k6-2026-10-14T13-57-09-484Z.json: 17 vertices, 42 edges. -/
def graph_ladder_n17_k6_2026_10_14T13_57_09_484Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 6), (0, 7), (0, 9), (0, 13), (1, 6), (1, 7), (1, 8), (1, 14), (1, 16), (2, 11), (2, 12), (2, 15), (2, 16), (3, 4), (3, 6), (3, 8), (3, 12), (3, 14), (4, 7), (4, 9), (4, 15), (4, 16), (5, 6), (5, 9), (5, 10), (5, 12), (5, 15), (6, 11), (7, 11), (7, 12), (8, 9), (8, 11), (8, 13), (9, 14), (10, 11), (10, 13), (10, 14), (10, 16), (12, 13), (13, 15), (14, 15)]

/-- ladder-n22-k7-2026-10-14T13-57-09-620Z.json: 22 vertices, 64 edges. -/
def graph_ladder_n22_k7_2026_10_14T13_57_09_620Z_edges : List (ℕ × ℕ) := [(0, 2), (0, 4), (0, 8), (0, 9), (0, 17), (0, 18), (1, 2), (1, 5), (1, 6), (1, 11), (1, 14), (1, 17), (2, 12), (2, 15), (2, 19), (2, 20), (3, 9), (3, 12), (3, 17), (3, 19), (3, 20), (4, 10), (4, 11), (4, 12), (4, 14), (4, 20), (5, 10), (5, 16), (5, 18), (5, 21), (6, 9), (6, 12), (6, 13), (6, 16), (6, 18), (7, 8), (7, 10), (7, 11), (7, 17), (7, 18), (7, 20), (8, 12), (8, 13), (8, 14), (8, 16), (9, 10), (9, 14), (9, 21), (10, 19), (11, 16), (11, 19), (11, 21), (12, 21), (13, 17), (13, 19), (13, 20), (13, 21), (14, 15), (14, 18), (15, 16), (15, 17), (15, 21), (16, 20), (18, 19)]

/-- ladder-n27-k8-2026-10-14T13-57-09-890Z.json: 27 vertices, 93 edges. -/
def graph_ladder_n27_k8_2026_10_14T13_57_09_890Z_edges : List (ℕ × ℕ) := [(0, 7), (0, 10), (0, 14), (0, 15), (0, 19), (0, 23), (0, 25), (1, 3), (1, 8), (1, 14), (1, 15), (1, 22), (1, 25), (1, 26), (2, 6), (2, 9), (2, 13), (2, 16), (2, 19), (2, 24), (2, 25), (3, 4), (3, 10), (3, 11), (3, 20), (3, 23), (3, 24), (4, 5), (4, 9), (4, 14), (4, 16), (4, 21), (4, 22), (5, 6), (5, 7), (5, 10), (5, 12), (5, 15), (5, 17), (6, 8), (6, 14), (6, 18), (6, 23), (6, 26), (7, 8), (7, 11), (7, 16), (7, 18), (7, 24), (8, 9), (8, 10), (8, 12), (8, 21), (9, 11), (9, 15), (9, 17), (9, 18), (10, 13), (10, 22), (10, 26), (11, 12), (11, 13), (11, 19), (11, 26), (12, 20), (12, 22), (12, 24), (12, 25), (13, 14), (13, 18), (13, 21), (13, 23), (14, 20), (14, 24), (15, 20), (15, 21), (16, 20), (16, 23), (16, 26), (17, 19), (17, 20), (17, 23), (17, 25), (17, 26), (18, 20), (18, 22), (18, 25), (19, 21), (19, 22), (21, 24), (21, 25), (22, 23), (24, 26)]

/-- ladder-n8-k4-2026-10-14T13-57-09-336Z.json: 8 vertices, 12 edges. -/
def graph_ladder_n8_k4_2026_10_14T13_57_09_336Z_edges : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 7), (1, 2), (1, 3), (2, 6), (2, 7), (3, 4), (3, 5), (4, 6), (5, 6), (5, 7)]

/-- test-n12-k5-plus1.json: 13 vertices, 26 edges. -/
def graph_test_n12_k5_plus1_edges : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 10), (0, 11), (1, 3), (1, 4), (1, 11), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 7), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9), (7, 10), (8, 10), (8, 11), (9, 11), (1, 12), (2, 12), (9, 12), (10, 12)]

-- Auxiliary definitions and lemmas used by the proofs below.

namespace GraphCheck

/-- number of set bits of `m` below `k` -/
def pcb (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => pcb m k + (if m.testBit k then 1 else 0)

theorem card_le_pcb (m : ℕ) : ∀ (k : ℕ) (S : Finset ℕ), (∀ j ∈ S, j < k ∧ m.testBit j = true) →
    S.card ≤ pcb m k := by
  intro k
  induction k with
  | zero =>
    intro S hS
    have : S = ∅ := by
      ext j; simp only [Finset.notMem_empty, iff_false]; intro hj; exact absurd (hS j hj).1 (by omega)
    simp [this]
  | succ k ih =>
    intro S hS
    simp only [pcb]
    by_cases hk : k ∈ S
    · have h1 := ih (S.erase k) (by
        intro j hj
        have := hS j (Finset.mem_of_mem_erase hj)
        exact ⟨by have := Finset.ne_of_mem_erase hj; omega, this.2⟩)
      have h2 := Finset.card_erase_add_one hk
      rw [if_pos (hS k hk).2]; omega
    · have h1 := ih S (by
        intro j hj
        have := hS j hj
        exact ⟨by have : j ≠ k := fun h => hk (h ▸ hj); omega, this.2⟩)
      omega

def go (am : List ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, need => need != 0
  | i + 1, cand, need =>
    if need = 0 then false
    else if pcb cand (i + 1) < need then true
    else if cand.testBit i then
      go am i (cand ^^^ (cand &&& am.getD i 0)) (need - 1) && go am i cand need
    else go am i cand need

theorem go_sound (am : List ℕ) : ∀ (i cand need : ℕ), go am i cand need = true →
    ∀ S : Finset ℕ, (∀ j ∈ S, j < i ∧ cand.testBit j = true) →
      (∀ a ∈ S, ∀ b ∈ S, (am.getD a 0).testBit b = false) → S.card < need := by
  intro i
  induction i with
  | zero =>
    intro cand need h S hS _
    have : S = ∅ := by
      ext j; simp only [Finset.notMem_empty, iff_false]; intro hj; exact absurd (hS j hj).1 (by omega)
    simp [go] at h; simp [this]; omega
  | succ i ih =>
    intro cand need h S hS hI
    simp only [go] at h
    split_ifs at h with h0 hp ht
    · have := card_le_pcb cand (i+1) S hS; omega
    · simp only [Bool.and_eq_true] at h
      by_cases hi : i ∈ S
      · have := ih _ _ h.1 (S.erase i) (by
          intro j hj
          have hjS := Finset.mem_of_mem_erase hj
          have hne := Finset.ne_of_mem_erase hj
          refine ⟨by have := (hS j hjS).1; omega, ?_⟩
          have hb := hI i hi j hjS
          rw [Nat.testBit_xor, Nat.testBit_land, (hS j hjS).2, hb]; rfl) (by
          intro a ha b hb
          exact hI a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb))
        have h2 := Finset.card_erase_add_one hi
        omega
      · exact ih _ _ h.2 S (by
          intro j hj
          exact ⟨by have : j ≠ i := fun e => hi (e ▸ hj); have := (hS j hj).1; omega, (hS j hj).2⟩) hI
    · exact ih _ _ h S (by
          intro j hj
          refine ⟨?_, (hS j hj).2⟩
          have : j ≠ i := fun e => ht (e ▸ (hS j hj).2)
          have := (hS j hj).1; omega) hI

def verifyMasks (n : ℕ) (E : List (ℕ × ℕ)) (am : List ℕ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    (am.getD i 0).testBit j == ((i, j) ∈ E || (j, i) ∈ E)

def triFree (n : ℕ) (am : List ℕ) : Bool :=
  (List.range n).all fun a => (List.range n).all fun b =>
    !((am.getD a 0).testBit b) || (am.getD a 0 &&& am.getD b 0) == 0

def check (n k : ℕ) (E : List (ℕ × ℕ)) (am : List ℕ) : Bool :=
  verifyMasks n E am && triFree n am && go am n (2 ^ n - 1) k

theorem verifyMasks_sound {n : ℕ} {E : List (ℕ × ℕ)} {am : List ℕ} (h : verifyMasks n E am = true)
    {i j : ℕ} (hi : i < n) (hj : j < n) : (am.getD i 0).testBit j = true ↔ Adj E i j := by
  simp only [verifyMasks, List.all_eq_true, List.mem_range] at h
  have := h i hi j hj
  simp only [beq_iff_eq] at this
  rw [this]; simp [Adj]

theorem check_sound {n k : ℕ} {E : List (ℕ × ℕ)} {am : List ℕ} (h : check n k E am = true) :
    TriangleFree n E ∧ NoStrangers n k E := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨hv, ht⟩, hg⟩ := h
  constructor
  · intro a b c hab hbc hac
    simp only [triFree, List.all_eq_true, List.mem_range] at ht
    have h1 := ht a a.2 b b.2
    rw [(verifyMasks_sound hv a.2 b.2).2 hab] at h1
    simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h1
    have h2 := (verifyMasks_sound hv a.2 c.2).2 hac
    have h3 : Adj E b c := hbc
    have h3 := (verifyMasks_sound hv b.2 c.2).2 h3
    have : (am.getD a 0 &&& am.getD b 0).testBit c = true := by
      rw [Nat.testBit_land, h2, h3]; rfl
    rw [h1] at this; simp at this
  · intro S hS
    by_contra hne
    push_neg at hne
    have := go_sound am n _ k hg (S.map Fin.valEmbedding) (by
      intro j hj
      simp only [Finset.mem_map, Fin.valEmbedding_apply] at hj
      obtain ⟨x, _, rfl⟩ := hj
      exact ⟨x.2, by simp [Nat.testBit_two_pow_sub_one, x.2]⟩) (by
      intro a ha b hb
      simp only [Finset.mem_map, Fin.valEmbedding_apply] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      have := hne x hx y hy
      rw [← verifyMasks_sound hv x.2 y.2] at this
      simpa using this)
    simp at this; omega

end GraphCheck

namespace WalkCount

def stepB (f : ℕ → ℕ → ℕ) (M q : ℕ) : ℕ := Nat.rec (f (M ||| 2^q) q) (fun _ _ => 0) ((M >>> q) % 2)

def dfsB : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | m+1, M, c => stepB (dfsB m) M (c+1) + stepB (dfsB m) M (c-1) + stepB (dfsB m) M (c+64) +
      stepB (dfsB m) M (c-64)

theorem stepB_eq (f : ℕ → ℕ → ℕ) (M q : ℕ) :
    stepB f M q = if M.testBit q = true then 0 else f (M ||| 2^q) q := by
  unfold stepB
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (M / 2^q) with h | h <;> simp [h]

/-- The good condition: from `p`, avoiding `V`, the walk's later positions are new and distinct. -/
def Good {m : ℕ} (V : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (s : Fin m → Fin 4) : Prop :=
  (∀ k : Fin m, p + pos s k.succ ∉ V) ∧ (∀ i j : Fin m, pos s i.succ = pos s j.succ → i = j)

open Classical in
noncomputable def A (m : ℕ) (V : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : ℕ :=
  (univ.filter (fun s : Fin m → Fin 4 => Good V p s)).card

theorem pos_zero {m : ℕ} (s : Fin m → Fin 4) : pos s 0 = 0 := by
  simp [pos]

theorem pos_cons_succ {m : ℕ} (d : Fin 4) (t : Fin m → Fin 4) (k : Fin (m + 1)) :
    pos (Fin.cons d t : Fin (m+1) → Fin 4) k.succ = dir d + pos t k := by
  simp only [pos]
  rw [Fin.sum_univ_succ]
  simp [Fin.val_succ]

theorem good_cons {m : ℕ} (V : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (d : Fin 4) (t : Fin m → Fin 4) :
    Good V p (Fin.cons d t : Fin (m+1) → Fin 4) ↔
      p + dir d ∉ V ∧ Good (insert (p + dir d) V) (p + dir d) t := by
  have key : ∀ k : Fin (m+1), pos (Fin.cons d t : Fin (m+1) → Fin 4) k.succ = dir d + pos t k :=
    pos_cons_succ d t
  constructor
  · rintro ⟨hV, hI⟩
    have h0 := hV 0
    rw [key, pos_zero, add_zero] at h0
    refine ⟨h0, fun k => ?_, fun i j h => ?_⟩
    · rw [Finset.mem_insert, not_or]
      constructor
      · intro h
        have hz : pos t k.succ = 0 := add_left_cancel (h.trans (add_zero _).symm)
        have := hI 0 k.succ (by rw [key, key, pos_zero, hz])
        exact Fin.succ_ne_zero k this.symm
      · have := hV k.succ
        rwa [key, ← add_assoc] at this
    · have := hI i.succ j.succ (by rw [key, key, h])
      exact Fin.succ_inj.mp this
  · rintro ⟨h0, hV, hI⟩
    refine ⟨fun k => ?_, fun i j h => ?_⟩
    · cases k using Fin.cases with
      | zero => rw [key, pos_zero, add_zero]; exact h0
      | succ k =>
        rw [key, ← add_assoc]
        exact fun hm => hV k (Finset.mem_insert_of_mem hm)
    · rw [key, key] at h
      have h' := add_left_cancel h
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          exfalso; apply hV j; rw [← h', pos_zero, add_zero]; exact Finset.mem_insert_self _ _
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          exfalso; apply hV i; rw [h', pos_zero, add_zero]; exact Finset.mem_insert_self _ _
        | succ j => rw [hI i j h']

theorem A_succ (m : ℕ) (V : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    A (m + 1) V p = ∑ d : Fin 4, if p + dir d ∈ V then 0 else A m (insert (p + dir d) V) (p + dir d) := by
  classical
  unfold A
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (m+1) => Fin 4).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  change (∑ t : Fin m → Fin 4, if Good V p (Fin.cons d t : Fin (m+1) → Fin 4) then 1 else 0) = _
  simp only [good_cons]
  split_ifs with h
  · simp [h]
  · simp only [h, not_false_eq_true, true_and]

def kap (q : ℤ × ℤ) : ℕ := (q.1 + 32 + 64 * (q.2 + 32)).toNat

def InBox (q : ℤ × ℤ) : Prop := -32 < q.1 ∧ q.1 < 32 ∧ -32 < q.2 ∧ q.2 < 32

theorem dfsB_eq : ∀ (m M : ℕ) (V : Finset (ℤ × ℤ)) (p : ℤ × ℤ),
    (-32 + (m : ℤ) < p.1 ∧ p.1 < 32 - m ∧ -32 + (m : ℤ) < p.2 ∧ p.2 < 32 - m) →
    (∀ q, InBox q → (M.testBit (kap q) = true ↔ q ∈ V)) →
    dfsB m M (kap p) = A m V p := by
  intro m
  induction m with
  | zero =>
    intro M V p _ _
    classical
    simp only [dfsB, A, Good]
    simp
  | succ m ih =>
    intro M V p hp hM
    have term : ∀ q : ℤ × ℤ, (-32 + (m : ℤ) < q.1 ∧ q.1 < 32 - m ∧ -32 + (m : ℤ) < q.2 ∧ q.2 < 32 - m) →
        stepB (dfsB m) M (kap q) = if q ∈ V then 0 else A m (insert q V) q := by
      intro q hq
      rw [stepB_eq]
      have hqb : InBox q := by unfold InBox; omega
      by_cases hqV : q ∈ V
      · rw [if_pos ((hM q hqb).2 hqV), if_pos hqV]
      · rw [if_neg (fun h => hqV ((hM q hqb).1 h)), if_neg hqV]
        apply ih _ _ _ hq
        intro r hr
        rw [Nat.testBit_lor, Nat.testBit_two_pow, Finset.mem_insert, Bool.or_eq_true, hM r hr,
          decide_eq_true_iff]
        constructor
        · rintro (h | h)
          · right; exact h
          · left
            unfold kap at h
            unfold InBox at hr hqb
            ext <;> omega
        · rintro (h | h)
          · right; rw [h]
          · left; exact h
    obtain ⟨p1, p2⟩ := p
    simp only at hp
    rw [A_succ, Fin.sum_univ_four]
    have d0 : dir 0 = (1, 0) := rfl
    have d1 : dir 1 = (-1, 0) := rfl
    have d2 : dir 2 = (0, 1) := rfl
    have d3 : dir 3 = (0, -1) := rfl
    simp only [dfsB, d0, d1, d2, d3, Prod.mk_add_mk, add_zero]
    have e1 : kap (p1, p2) + 1 = kap (p1 + 1, p2) := by unfold kap; simp only; omega
    have e2 : kap (p1, p2) - 1 = kap (p1 + -1, p2) := by unfold kap; simp only; omega
    have e3 : kap (p1, p2) + 64 = kap (p1, p2 + 1) := by unfold kap; simp only; omega
    have e4 : kap (p1, p2) - 64 = kap (p1, p2 + -1) := by unfold kap; simp only; omega
    rw [e1, e2, e3, e4, term _ (by simp only; push_cast at hp ⊢; omega),
      term _ (by simp only; push_cast at hp ⊢; omega), term _ (by simp only; push_cast at hp ⊢; omega),
      term _ (by simp only; push_cast at hp ⊢; omega)]

theorem selfAvoiding_eq (n : ℕ) (hn : n < 32) : selfAvoiding n = dfsB n (2 ^ 2080) 2080 := by
  have h1 : selfAvoiding n = A n {0} 0 := by
    classical
    unfold selfAvoiding A
    congr 1
    apply Finset.filter_congr
    intro s _
    constructor
    · intro hinj
      refine ⟨fun k hk => ?_, fun i j h => Fin.succ_inj.mp (hinj h)⟩
      rw [zero_add, Finset.mem_singleton, ← pos_zero s] at hk
      exact Fin.succ_ne_zero k (hinj hk)
    · rintro ⟨hV, hI⟩ i j h
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j => exfalso; apply hV j; rw [zero_add, ← h, pos_zero]; exact Finset.mem_singleton_self _
      | succ i =>
        cases j using Fin.cases with
        | zero => exfalso; apply hV i; rw [zero_add, h, pos_zero]; exact Finset.mem_singleton_self _
        | succ j => rw [hI i j h]
  rw [h1, ← dfsB_eq n (2 ^ 2080) {0} 0 (by simp only [Prod.fst_zero, Prod.snd_zero]; omega)]
  · rfl
  · intro q hq
    rw [Nat.testBit_two_pow, decide_eq_true_iff, Finset.mem_singleton]
    unfold kap InBox at *
    constructor
    · intro h; ext <;> simp <;> omega
    · rintro rfl; simp

end WalkCount

namespace Prob

theorem rowChance_eq {n : ℕ} (q : ℚ) (x : Fin n → Bool) :
    rowChance q x = q ^ heads x * (1 - q) ^ (n - heads x) := by
  unfold rowChance heads
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => x i = true)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  simp only [Bool.not_eq_true] at this ⊢
  omega

/-- `Fin n → Bool` is the same as subsets of `Fin n`. -/
def boolEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun x := univ.filter (fun i => x i = true)
  invFun S := fun i => decide (i ∈ S)
  left_inv x := by ext i; simp
  right_inv S := by ext i; simp

theorem sum_heads {n : ℕ} (g : ℕ → ℚ) :
    ∑ x : Fin n → Bool, g (heads x) = ∑ k ∈ range (n + 1), (n.choose k : ℚ) * g k := by
  rw [← (boolEquiv n).symm.sum_comp]
  have h1 : ∀ S : Finset (Fin n), heads ((boolEquiv n).symm S) = S.card := by
    intro S; simp [heads, boolEquiv]
  simp only [h1]
  have := Finset.sum_powerset_apply_card (f := g) (x := (univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at this
  rw [this]
  simp [nsmul_eq_mul]

theorem sum_heads_rowChance {n : ℕ} (q : ℚ) (f : ℕ → ℚ) :
    ∑ x : Fin n → Bool, f (heads x) * rowChance q x =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (f k * (q ^ k * (1 - q) ^ (n - k))) := by
  simp only [rowChance_eq]
  exact sum_heads (fun k => f k * (q ^ k * (1 - q) ^ (n - k)))

end Prob

namespace Dice

noncomputable def N (n s : ℕ) : ℕ := (univ.filter (fun f : Fin n → Fin 6 => (∑ i, (f i).val) ≤ s)).card

theorem N_succ (n s : ℕ) : N (n + 1) s = ∑ a : Fin 6, if a.val ≤ s then N n (s - a.val) else 0 := by
  unfold N
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ : Fin (n+1) => Fin 6).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  change (∑ t : Fin n → Fin 6, if (∑ i, ((Fin.cons a t : Fin (n+1) → Fin 6) i).val) ≤ s then 1 else 0) = _
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  split_ifs with h
  · refine Finset.sum_congr rfl fun t _ => ?_
    have : a.val + ∑ i, (t i).val ≤ s ↔ ∑ i, (t i).val ≤ s - a.val := by omega
    simp only [this]
  · rw [Finset.sum_eq_zero]
    intro t _
    rw [if_neg (by omega)]

def stepL (l : List ℕ) : List ℕ :=
  (List.range 11).map (fun s => ((List.range 6).map (fun a => if a ≤ s then l.getD (s-a) 0 else 0)).sum)

def Dl : ℕ → List ℕ
  | 0 => List.replicate 11 1
  | n+1 => stepL (Dl n)

theorem N_eq (n : ℕ) : ∀ s, s < 11 → N n s = (Dl n).getD s 0 := by
  induction n with
  | zero =>
    intro s hs
    simp only [Dl, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hs, Option.getD_some]
    unfold N
    rw [Finset.card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _; simp
  | succ n ih =>
    intro s hs
    rw [N_succ, Dl, stepL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]
    simp only [Option.map_some, Option.getD_some]
    simp only [Fin.sum_univ_six, List.range_succ, List.range_zero, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
    have e : ∀ a, a < 6 → (if a ≤ s then N n (s - a) else 0) = (if a ≤ s then (Dl n).getD (s - a) 0 else 0) := by
      intro a ha
      split_ifs with h
      · exact ih _ (by omega)
      · rfl
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    rw [e _ (Fin.isLt 3), e _ (Fin.isLt 4), e _ (Fin.isLt 5)]
    simp only [add_assoc, add_zero]
    rfl

end Dice

namespace PermCount
open Equiv

theorem card_fix {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    (univ.filter (fun τ : Perm α => ∀ x ∈ S, τ x = x)).card = (Fintype.card α - S.card).factorial := by
  rw [← Fintype.card_subtype]
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun x : α => x ∉ S)
  have h2 : Fintype.card {τ : Perm α // ∀ x ∈ S, τ x = x} =
      Fintype.card {f : Perm α // ∀ a, ¬ (a ∉ S) → f a = a} := by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro σ
    simp only [not_not]
  rw [h2, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_coe]

theorem card_fiber {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (g : S → α)
    (hg : Function.Injective g) :
    (univ.filter (fun σ : Perm α => ∀ x : S, σ x = g x)).card = (Fintype.card α - S.card).factorial := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ Set.range g} := Equiv.ofInjective g hg
  let σ0 : Perm α := e.extendSubtype
  have h0 : ∀ x : S, σ0 x = g x := by
    intro x
    simp only [σ0, Equiv.extendSubtype_apply_of_mem e x x.2]
    simp [e]
  rw [← card_fix S]
  apply Finset.card_nbij' (fun σ => σ0⁻¹ * σ) (fun τ => σ0 * τ)
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    intro x hx
    rw [Perm.mul_apply, hσ ⟨x, hx⟩, ← h0 ⟨x, hx⟩]; simp
  · intro τ hτ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
    intro x
    rw [Perm.mul_apply, hτ x x.2, h0]
  · intro σ _; simp
  · intro τ _; simp

theorem card_maps_into {α : Type*} [Fintype α] [DecidableEq α] (S T : Finset α) :
    (univ.filter (fun σ : Perm α => ∀ x ∈ S, σ x ∈ T)).card =
      T.card.descFactorial S.card * (Fintype.card α - S.card).factorial := by
  classical
  let t : Finset (S → α) := univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ T)
  have hmaps : ((univ.filter (fun σ : Perm α => ∀ x ∈ S, σ x ∈ T) : Finset (Perm α)) : Set (Perm α)).MapsTo
      (fun σ => fun x : S => σ x) t := by
    intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hσ
    simp only [t, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨fun a b h => Subtype.ext (σ.injective h), fun x => hσ x x.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ g ∈ t, ((univ.filter (fun σ : Perm α => ∀ x ∈ S, σ x ∈ T)).filter
      (fun σ => (fun x : S => σ x) = g)).card = (Fintype.card α - S.card).factorial := by
    intro g hg
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    rw [← card_fiber S g hg.1]
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩ x; rw [← h]
    · intro h
      refine ⟨fun x hx => ?_, funext h⟩
      rw [h ⟨x, hx⟩]; exact hg.2 _
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  congr 1
  have : t.card = Fintype.card (S ↪ T) := by
    rw [← Fintype.card_coe t]
    apply Fintype.card_congr
    exact {
      toFun := fun g => ⟨fun x => ⟨g.1 x, ((Finset.mem_filter.mp g.2).2).2 x⟩, fun a b h => by
        have := congrArg Subtype.val h
        exact ((Finset.mem_filter.mp g.2).2).1 this⟩
      invFun := fun f => ⟨fun x => (f x).1, by
        simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun a b h => f.injective (Subtype.ext h), fun x => (f x).2⟩⟩
      left_inv := fun g => by ext; rfl
      right_inv := fun f => by ext; rfl }
  rw [this, Fintype.card_embedding_eq]
  simp

end PermCount

theorem PermCount.firstPlace_sum {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ∑ σ : Equiv.Perm (Fin n), firstPlace σ p =
      Fintype.card (Equiv.Perm (Fin n)) + ∑ i : Fin n,
        (univ.filter (fun c => ¬ p c)).card.descFactorial (i.val + 1) * (n - (i.val + 1)).factorial := by
  unfold firstPlace
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  refine congrArg (Fintype.card (Equiv.Perm (Fin n)) + ·) ?_
  conv_lhs => simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.card_filter]
  have hS : (univ.filter (fun j : Fin n => j ≤ i)).card = i.val + 1 := by
    rw [show (univ.filter (fun j : Fin n => j ≤ i)) = Finset.Iic i by ext; simp]
    simp
  have := PermCount.card_maps_into (α := Fin n) (univ.filter (fun j => j ≤ i))
    (univ.filter (fun c => ¬ p c))
  rw [hS, Fintype.card_fin] at this
  rw [← this]
  apply congrArg Finset.card
  ext σ
  simp

theorem PermCount.firstPlace_sum' {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    ∑ σ : Equiv.Perm (Fin n), firstPlace σ p =
      n.factorial + ∑ i ∈ range n,
        (univ.filter (fun c => ¬ p c)).card.descFactorial (i + 1) * (n - (i + 1)).factorial := by
  rw [PermCount.firstPlace_sum, Fintype.card_perm, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun i => (univ.filter (fun c => ¬ p c)).card.descFactorial (i + 1) * (n - (i + 1)).factorial)]

theorem filter_card_eq_iff {α : Type*} [Fintype α] [DecidableEq α] (h : Finset α) (p : α → Prop)
    [DecidablePred p] : (h.filter p).card = (univ.filter p).card ↔ univ.filter p ⊆ h := by
  have hsub : h.filter p ⊆ univ.filter p := Finset.filter_subset_filter _ (Finset.subset_univ _)
  constructor
  · intro hc x hx
    have heq := Finset.eq_of_subset_of_card_le hsub hc.ge
    rw [← heq] at hx
    exact (Finset.mem_filter.mp hx).1
  · intro hs
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hx
    exact hs (by simp [hx])

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_amcs_n13_k5_2026_10_15T01_53_33_663Z :
    GraphCheck.check 13 5 graph_amcs_n13_k5_2026_10_15T01_53_33_663Z_edges
      [86, 1793, 4481, 848, 2185, 2752, 1065, 1076, 2062, 4138, 4290, 4400, 3588] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_amcs_n13_k5_2026_10_15T01_54_36_788Z :
    GraphCheck.check 13 5 graph_amcs_n13_k5_2026_10_15T01_54_36_788Z_edges
      [1062, 6657, 705, 1632, 2400, 153, 4124, 6180, 5648, 270, 2313, 1170, 450] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_amcs_n17_k6_2026_10_15T01_53_33_852Z :
    GraphCheck.check 17 6 graph_amcs_n17_k6_2026_10_15T01_53_33_852Z_edges
      [49800, 36480, 8760, 67845, 33860, 69764, 68240, 355, 13448, 4167, 82194, 20554, 35616, 114948, 11265, 12307, 9320] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_amcs_n17_k6_2026_10_15T01_54_36_944Z :
    GraphCheck.check 17 6 graph_amcs_n17_k6_2026_10_15T01_54_36_944Z_edges
      [74370, 121, 67736, 12550, 49670, 3458, 39170, 49189, 66152, 6417, 102432, 8804, 17992, 51209, 77968, 9424, 17669] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_amcs_n22_k7_2026_10_15T01_54_54_955Z :
    GraphCheck.check 22 7 graph_amcs_n22_k7_2026_10_15T01_54_54_955Z_edges
      [66188, 287552, 3166225, 1853441, 559492, 2189568, 3344386, 402449, 1179698, 2132995, 1655424, 4728, 985092, 1605794, 132142, 467472, 37985, 53696, 2134154, 2110488, 9548, 787044] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_amcs_n8_k4_2026_10_15T01_53_33_552Z :
    GraphCheck.check 8 4 graph_amcs_n8_k4_2026_10_15T01_53_33_552Z_edges
      [50, 13, 194, 146, 73, 193, 52, 44] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_amcs_n8_k4_2026_10_15T01_54_36_642Z :
    GraphCheck.check 8 4 graph_amcs_n8_k4_2026_10_15T01_54_36_642Z_edges
      [88, 20, 194, 129, 35, 208, 37, 44] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T13_56_23_903Z :
    GraphCheck.check 13 5 graph_anneal_n13_k5_2026_10_14T13_56_23_903Z_edges
      [2224, 2400, 4200, 2692, 833, 519, 1046, 1289, 4242, 1080, 4800, 4107, 3332] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T14_06_17_873Z :
    GraphCheck.check 13 5 graph_anneal_n13_k5_2026_10_14T14_06_17_873Z_edges
      [2224, 2400, 4200, 2692, 833, 519, 1046, 1289, 4242, 1080, 4800, 4107, 3332] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T15_10_04_875Z :
    GraphCheck.check 13 5 graph_anneal_n13_k5_2026_10_14T15_10_04_875Z_edges
      [2224, 2400, 4200, 2692, 833, 519, 1046, 1289, 4242, 1080, 4800, 4107, 3332] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T15_11_12_007Z :
    GraphCheck.check 13 5 graph_anneal_n13_k5_2026_10_14T15_11_12_007Z_edges
      [2224, 2400, 4200, 2692, 833, 519, 1046, 1289, 4242, 1080, 4800, 4107, 3332] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T15_23_48_940Z :
    GraphCheck.check 13 5 graph_anneal_n13_k5_2026_10_14T15_23_48_940Z_edges
      [2224, 2400, 4200, 2692, 833, 519, 1046, 1289, 4242, 1080, 4800, 4107, 3332] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T13_56_23_520Z :
    GraphCheck.check 13 5 graph_circulant_n13_k5_2026_10_14T13_56_23_520Z_edges
      [3084, 6168, 4145, 99, 198, 396, 792, 1584, 3168, 6336, 4481, 771, 1542] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T14_06_20_071Z :
    GraphCheck.check 13 5 graph_circulant_n13_k5_2026_10_14T14_06_20_071Z_edges
      [3084, 6168, 4145, 99, 198, 396, 792, 1584, 3168, 6336, 4481, 771, 1542] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T15_10_07_045Z :
    GraphCheck.check 13 5 graph_circulant_n13_k5_2026_10_14T15_10_07_045Z_edges
      [3084, 6168, 4145, 99, 198, 396, 792, 1584, 3168, 6336, 4481, 771, 1542] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T15_11_14_178Z :
    GraphCheck.check 13 5 graph_circulant_n13_k5_2026_10_14T15_11_14_178Z_edges
      [3084, 6168, 4145, 99, 198, 396, 792, 1584, 3168, 6336, 4481, 771, 1542] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T15_23_51_122Z :
    GraphCheck.check 13 5 graph_circulant_n13_k5_2026_10_14T15_23_51_122Z_edges
      [3084, 6168, 4145, 99, 198, 396, 792, 1584, 3168, 6336, 4481, 771, 1542] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T13_56_23_372Z :
    GraphCheck.check 8 4 graph_circulant_n8_k4_2026_10_14T13_56_23_372Z_edges
      [146, 37, 74, 148, 41, 82, 164, 73] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T14_06_20_015Z :
    GraphCheck.check 8 4 graph_circulant_n8_k4_2026_10_14T14_06_20_015Z_edges
      [146, 37, 74, 148, 41, 82, 164, 73] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T15_10_06_995Z :
    GraphCheck.check 8 4 graph_circulant_n8_k4_2026_10_14T15_10_06_995Z_edges
      [146, 37, 74, 148, 41, 82, 164, 73] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T15_11_14_131Z :
    GraphCheck.check 8 4 graph_circulant_n8_k4_2026_10_14T15_11_14_131Z_edges
      [146, 37, 74, 148, 41, 82, 164, 73] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T15_23_51_067Z :
    GraphCheck.check 8 4 graph_circulant_n8_k4_2026_10_14T15_23_51_067Z_edges
      [146, 37, 74, 148, 41, 82, 164, 73] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_grown_n13_k5_1791990648209 :
    GraphCheck.check 13 5 graph_grown_n13_k5_1791990648209_edges
      [3084, 6168, 4145, 99, 198, 396, 792, 1584, 3168, 6336, 4481, 771, 1542] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_ladder_n13_k5_2026_10_14T13_57_09_399Z :
    GraphCheck.check 13 5 graph_ladder_n13_k5_2026_10_14T13_57_09_399Z_edges
      [2584, 3084, 834, 4131, 5185, 1352, 180, 6720, 6180, 1157, 562, 387, 408] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_ladder_n17_k6_2026_10_14T13_57_09_484Z :
    GraphCheck.check 17 6 graph_ladder_n17_k6_2026_10_14T13_57_09_484Z_edges
      [8900, 82368, 104449, 20816, 98952, 38464, 2091, 6163, 10762, 16689, 92192, 1476, 8364, 38145, 34314, 24628, 1046] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_ladder_n22_k7_2026_10_14T13_57_09_620Z :
    GraphCheck.check 22 7 graph_ladder_n22_k7_2026_10_14T13_57_09_620Z_edges
      [394004, 149604, 1609731, 1708544, 1072129, 2425858, 340482, 1445120, 94337, 2114633, 524976, 2687122, 2097500, 3801408, 295698, 2310148, 1083744, 41099, 540897, 273420, 73884, 47648] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_ladder_n27_k8_2026_10_14T13_57_09_890Z :
    GraphCheck.check 27 8 graph_ladder_n27_k8_2026_10_14T13_57_09_890Z_edges
      [42517632, 104907016, 50930240, 26217490, 6373928, 169168, 75776292, 17107233, 2102978, 428308, 71311657, 67646088, 55576864, 10767364, 17834067, 3146275, 76546196, 110625312, 38806208, 6424581, 512008, 50897168, 9180178, 4399177, 69226636, 2494471, 16976962] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_ladder_n8_k4_2026_10_14T13_57_09_336Z :
    GraphCheck.check 8 4 graph_ladder_n8_k4_2026_10_14T13_57_09_336Z_edges
      [146, 13, 194, 50, 73, 200, 52, 37] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_test_n12_k5_plus1 :
    GraphCheck.check 13 5 graph_test_n12_k5_plus1_edges
      [3084, 6168, 4145, 99, 198, 396, 792, 1584, 3168, 6336, 4481, 771, 1542] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n35_k9_2026_10_14T13_56_47_249Z :
    GraphCheck.check 35 9 graph_circulant_n35_k9_2026_10_14T13_56_47_249Z_edges
      [3019899600, 6039799200, 12079598400, 24159196800, 13958655233, 27917310466, 21474882565, 8590026763, 17180053526, 368685, 737370, 1474740, 2949480, 5898960, 11797920, 23595840, 47191680, 94383360, 188766720, 377533440, 755066880, 1510133760, 3020267520, 6040535040, 12081070080, 24162140160, 13964541953, 27929083906, 21498429445, 8637120523, 17274241046, 188743725, 377487450, 754974900, 1509949800] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_circulant_n38_k10_2026_10_14T13_56_49_410Z :
    GraphCheck.check 38 10 graph_circulant_n38_k10_2026_10_14T13_56_49_410Z_edges
      [7114066624, 14228133248, 28456266496, 56912532992, 113825065984, 227650131968, 180422356993, 85966807043, 171933614086, 68989321229, 137978642458, 1079377973, 2158755946, 4317511892, 8635023784, 17270047568, 34540095136, 69080190272, 138160380544, 1442854145, 2885708290, 5771416580, 11542833160, 23085666320, 46171332640, 92342665280, 184685330560, 94492754177, 188985508354, 103093109765, 206186219530, 137494532117, 111157291, 222314582, 444629164, 889258328, 1778516656, 3557033312] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_exoo_n39_k10 :
    GraphCheck.check 39 10 graph_exoo_n39_k10_edges
      [8665465938, 17330931845, 138782314762, 2686722580, 347926446121, 17718973008, 69831237793, 2223522114, 279323903620, 146298439976, 71408568577, 4336948738, 283551803428, 154754240584, 1344545936, 17450993921, 70334452226, 2189762596, 279257432136, 8725496976, 279259390468, 77448921128, 429775717440, 70351194241, 139629695234, 9210824784, 154787909761, 35771654402, 71542292996, 38965150760, 294347948100, 5654054024, 148714555664, 55870755329, 78454497314, 490297360384, 51818595408, 38742794756, 35438989584] = true :=
  by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem GraphCheck.cert_graph_grown_n36_k10_1791990649104 :
    GraphCheck.check 36 10 graph_grown_n36_k10_1791990649104_edges
      [38835323392, 6520047744, 37480334368, 17721986176, 38654711616, 4362735812, 2709536816, 42983490346, 682688656, 889847953, 1082540060, 35567865866, 314845232, 52093915136, 235504704, 17209509892, 41087549696, 8625663520, 2687538305, 3224396320, 8708161800, 34650063106, 10806661129, 8589972803, 1211212352, 1074942085, 51544867362, 25786599685, 25771971076, 5368980300, 26357533696, 17184915526, 26306740275, 5785124992, 7985995784, 69281941] = true :=
  by decide +kernel

-- THEOREMS

-- BEGIN p05_birthday_problem
/-- 23 people, birthdays uniform on 365 days: the chance two share a day. -/
theorem p05_birthday_problem :
    ((univ.filter (fun f : Fin 23 → Fin 365 => ¬ Function.Injective f)).card : ℚ) / 365 ^ 23 = (38093904702297390785243708291056390518886454060947061 : ℚ) / 75091883268515350125426207425223147563269805908203125 := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_subtype_compl, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
      Fintype.card_embedding_eq, Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [Nat.cast_sub (Nat.descFactorial_le_pow _ _)]
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
  norm_num
-- END p05_birthday_problem

-- BEGIN p13_cards_to_first_ace
/-- a shuffled 52-card deck: the average place of the first ace. -/
theorem p13_cards_to_first_ace :
    (∑ σ : Equiv.Perm (Fin 52), (firstPlace σ (fun c => rank c = 1) : ℚ)) / (Fintype.card (Equiv.Perm (Fin 52)) : ℚ) = (53 : ℚ) / 5 := by
  have key := PermCount.firstPlace_sum' (n := 52) (fun c => rank c = 1)
  have hA : (univ.filter (fun c : Fin 52 => ¬ rank c = 1)).card = 48 := by decide
  rw [hA] at key
  rw [Fintype.card_perm, Fintype.card_fin]
  have hnum : (Nat.factorial 52 + ∑ i ∈ range 52, (48 : ℕ).descFactorial (i + 1) * (52 - (i + 1)).factorial) * 5
      = 53 * Nat.factorial 52 := by decide +kernel
  have : ((∑ σ : Equiv.Perm (Fin 52), firstPlace σ (fun c => rank c = 1) : ℕ) : ℚ) * 5 = 53 * (Nat.factorial 52 : ℚ) := by
    rw [key]; exact_mod_cast hnum
  push_cast at this
  have hf : (Nat.factorial 52 : ℚ) ≠ 0 := by positivity
  field_simp
  linarith
-- END p13_cards_to_first_ace

-- BEGIN p17_three_of_five_vote
/-- five coins, each heads with chance 3/5: the chance of at least three heads. -/
theorem p17_three_of_five_vote :
    (∑ x : Fin 5 → Bool, if 3 ≤ heads x then rowChance (3 / 5) x else 0) = (2133 : ℚ) / 3125 := by
  have := Prob.sum_heads_rowChance (n := 5) (3/5) (fun k => if 3 ≤ k then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at this
  rw [this]
  simp [Finset.sum_range_succ, Nat.choose]
  norm_num
-- END p17_three_of_five_vote

-- BEGIN p21_rare_one_in_1000
/-- a whole number uniform on 0 to 999: the chance it is 0. -/
theorem p21_rare_one_in_1000 :
    ((univ.filter (fun x : Fin 1000 => x.val = 0)).card : ℚ) / 1000 = (1 : ℚ) / 1000 := by
  have : (univ.filter (fun x : Fin 1000 => x.val = 0)) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩
  rw [this, Finset.card_singleton]
  norm_num
-- END p21_rare_one_in_1000

-- BEGIN p22_st_petersburg_capped
/-- flips until the first head (chance 1/2 each): the average of 2 to the power of that count, capped at 20. -/
theorem p22_st_petersburg_capped :
    (∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) * 2 ^ (min (j + 1) 20)) = (21 : ℝ) := by
  set f : ℕ → ℝ := fun j => ((1 : ℝ) / 2) ^ (j + 1) * 2 ^ (min (j + 1) 20) with hf
  have tail : ∀ i, f (i + 19) = ((1 : ℝ) / 2) ^ i := by
    intro i
    simp only [hf]
    rw [show min (i + 19 + 1) 20 = 20 by omega, show i + 19 + 1 = i + 20 by omega, pow_add,
      mul_assoc, ← mul_pow]
    norm_num
  have hs : Summable f := by
    rw [← summable_nat_add_iff 19]
    simp_rw [tail]
    exact summable_geometric_two
  rw [← hs.sum_add_tsum_nat_add 19]
  simp_rw [tail]
  rw [tsum_geometric_two]
  simp [hf, Finset.sum_range_succ]
  norm_num
-- END p22_st_petersburg_capped

-- BEGIN p48_third_success_by_twelve
/-- twelve coins, each heads with chance 1/3: the chance of at least three heads. -/
theorem p48_third_success_by_twelve :
    (∑ x : Fin 12 → Bool, if 3 ≤ heads x then rowChance (1 / 3) x else 0) = (435185 : ℚ) / 531441 := by
  have := Prob.sum_heads_rowChance (n := 12) (1/3) (fun k => if 3 ≤ k then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at this
  rw [this]
  simp [Finset.sum_range_succ, Nat.choose]
  norm_num
-- END p48_third_success_by_twelve

-- BEGIN p65_trap_bridge_aces_kings
/-- a 13-card hand from 52: the chance it holds all four aces and all four kings. -/
theorem p65_trap_bridge_aces_kings :
    (((powersetCard 13 (univ : Finset (Fin 52))).filter (fun h => (h.filter (fun c => rank c = 1)).card = 4 ∧ (h.filter (fun c => rank c = 13)).card = 4)).card : ℚ) / (Nat.choose 52 13 : ℚ) = (11 : ℚ) / 6431950 := by
  obtain ⟨A, hA⟩ : ∃ A, A = (univ : Finset (Fin 52)).filter (fun c => rank c = 1) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = (univ : Finset (Fin 52)).filter (fun c => rank c = 13) := ⟨_, rfl⟩
  have cA : A.card = 4 := by rw [hA]; decide
  have cK : K.card = 4 := by rw [hK]; decide
  have cC : (univ \ (A ∪ K)).card = 44 := by rw [hA, hK]; decide
  have e : (powersetCard 13 (univ : Finset (Fin 52))).filter (fun h => (h.filter (fun c => rank c = 1)).card = 4 ∧ (h.filter (fun c => rank c = 13)).card = 4) =
      (powersetCard 13 (univ : Finset (Fin 52))).filter (fun h => A ∪ K ⊆ h) := by
    apply Finset.filter_congr
    intro h _
    rw [Finset.union_subset_iff, hA, hK, ← filter_card_eq_iff, ← filter_card_eq_iff, ← hA, ← hK, cA, cK]
  have hc : ((powersetCard 13 (univ : Finset (Fin 52))).filter (fun h => A ∪ K ⊆ h)).card =
      (powersetCard 5 (univ \ (A ∪ K))).card := by
    have cAK : (A ∪ K).card = 8 := by rw [hA, hK]; decide
    apply Finset.card_bij' (fun h _ => h \ (A ∪ K)) (fun t _ => t ∪ (A ∪ K))
    · intro h hh
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hh
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _), ?_⟩
      rw [Finset.card_sdiff_of_subset hh.2, hh.1.2, cAK]
    · intro t ht
      rw [Finset.mem_powersetCard] at ht
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      have hd : Disjoint t (A ∪ K) := by
        rw [Finset.disjoint_left]; intro x hx hx'
        have := ht.1 hx; simp at this; exact (Finset.mem_union.mp hx').elim this.1 this.2
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right⟩
      rw [Finset.card_union_of_disjoint hd, ht.2, cAK]
    · intro h hh
      rw [Finset.mem_filter] at hh
      exact Finset.sdiff_union_of_subset hh.2
    · intro t ht
      rw [Finset.mem_powersetCard] at ht
      have hd : Disjoint t (A ∪ K) := by
        rw [Finset.disjoint_left]; intro x hx hx'
        have := ht.1 hx; simp at this; exact (Finset.mem_union.mp hx').elim this.1 this.2
      exact Finset.union_sdiff_cancel_right hd
  rw [e, hc, Finset.card_powersetCard, cC]
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num : 5 ≤ 44),
    Nat.choose_eq_factorial_div_factorial (by norm_num : 13 ≤ 52)]
  rw [show Nat.factorial 44 / (Nat.factorial 5 * Nat.factorial (44 - 5)) = 1086008 by decide +kernel,
    show Nat.factorial 52 / (Nat.factorial 13 * Nat.factorial (52 - 13)) = 635013559600 by decide +kernel]
  norm_num
-- END p65_trap_bridge_aces_kings

-- BEGIN p65_trap_medical_test_positive
/-- sick with chance 1/1000; a sick person tests positive with chance 99/100, a well one with 1/100: given a positive test, the chance of being sick. -/
theorem p65_trap_medical_test_positive :
    (∑ s : Bool, ∑ a : Bool, ∑ b : Bool, if s = true ∧ (if s then a else b) = true then (if s then (1 : ℚ) / 1000 else 999 / 1000) * (if a then 99 / 100 else 1 / 100) * (if b then 1 / 100 else 99 / 100) else 0) / (∑ s : Bool, ∑ a : Bool, ∑ b : Bool, if (if s then a else b) = true then (if s then (1 : ℚ) / 1000 else 999 / 1000) * (if a then 99 / 100 else 1 / 100) * (if b then 1 / 100 else 99 / 100) else 0) = (11 : ℚ) / 122 := by
  simp only [Fintype.sum_bool]
  norm_num
-- END p65_trap_medical_test_positive

-- BEGIN p68_trap_common_shock_failure
/-- one coin with chance 1/1000, or else all five of five coins with chance 1/100 each: the chance of either. -/
theorem p68_trap_common_shock_failure :
    (∑ a : Bool, ∑ x : Fin 5 → Bool, if a = true ∨ heads x = 5 then (if a then (1 : ℚ) / 1000 else 999 / 1000) * rowChance (1 / 100) x else 0) = (10000000999 : ℚ) / 10000000000000 := by
  rw [Fintype.sum_bool]
  simp only [true_or, if_true, false_or, Bool.false_eq_true, if_false]
  rw [← Finset.mul_sum]
  have h1 := Prob.sum_heads_rowChance (n := 5) (1/100) (fun _ => 1)
  have h2 := Prob.sum_heads_rowChance (n := 5) (1/100) (fun k => if k = 5 then 1 else 0)
  simp only [one_mul, ite_mul, zero_mul] at h1 h2
  have h3 : ∀ x : Fin 5 → Bool, (if heads x = 5 then (999 / 1000 : ℚ) * rowChance (1 / 100) x else 0) =
      999 / 1000 * (if heads x = 5 then rowChance (1 / 100) x else 0) := by
    intro x; split_ifs <;> simp
  simp only [h3, ← Finset.mul_sum, h1, h2]
  simp [Finset.sum_range_succ, Nat.choose]
  norm_num
-- END p68_trap_common_shock_failure

-- BEGIN p69_trap_twenty_dice_low_tail
/-- twenty fair dice: the chance their total is 30 or less. -/
theorem p69_trap_twenty_dice_low_tail :
    ((univ.filter (fun f : Fin 20 → Fin 6 => (∑ i, (f i).val) + 20 ≤ 30)).card : ℚ) / 6 ^ 20 = (9944165 : ℚ) / 1218719480020992 := by
  have h1 : (univ.filter (fun f : Fin 20 → Fin 6 => (∑ i, (f i).val) + 20 ≤ 30)).card = Dice.N 20 10 := by
    unfold Dice.N
    simp only [show ∀ x : ℕ, x + 20 ≤ 30 ↔ x ≤ 10 from fun x => by omega]
  have h2 : (Dice.Dl 20).getD 10 0 = 29832495 := by decide +kernel
  rw [h1, Dice.N_eq 20 10 (by norm_num), h2]
  norm_num
-- END p69_trap_twenty_dice_low_tail

-- BEGIN p69_trap_two_records_in_row
/-- a shuffle of 101 cards: the chance the highest card sits last and the second highest just before it. -/
theorem p69_trap_two_records_in_row :
    ((univ.filter (fun σ : Equiv.Perm (Fin 101) => σ 100 = 100 ∧ σ 99 = 99)).card : ℚ) / (Fintype.card (Equiv.Perm (Fin 101)) : ℚ) = (1 : ℚ) / 10100 := by
  have h1 : (univ.filter (fun σ : Equiv.Perm (Fin 101) => σ 100 = 100 ∧ σ 99 = 99)).card =
      Nat.factorial 99 := by
    rw [← Fintype.card_subtype]
    have e := Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin 101 => x ≠ 100 ∧ x ≠ 99)
    have h2 : Fintype.card {σ : Equiv.Perm (Fin 101) // σ 100 = 100 ∧ σ 99 = 99} =
        Fintype.card {f : Equiv.Perm (Fin 101) // ∀ a, ¬ (a ≠ 100 ∧ a ≠ 99) → f a = a} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro σ
      constructor
      · rintro ⟨h1, h2⟩ a ha
        by_cases h : a = 100
        · rw [h, h1]
        · have : a = 99 := by tauto
          rw [this, h2]
      · intro h
        exact ⟨h 100 (by simp), h 99 (by simp)⟩
    rw [h2, ← Fintype.card_congr e, Fintype.card_perm]
    congr 1
  rw [h1, Fintype.card_perm, Fintype.card_fin]
  rw [show Nat.factorial 101 = 101 * 100 * Nat.factorial 99 by
    rw [Nat.factorial_succ, Nat.factorial_succ]; ring]
  push_cast
  have : (Nat.factorial 99 : ℚ) ≠ 0 := by positivity
  field_simp
-- END p69_trap_two_records_in_row

-- BEGIN walks_0
/-- square-grid walks of 0 steps that never revisit a point (OEIS A001411). -/
theorem walks_0 :
    selfAvoiding 0 = 1 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 0 (by norm_num)]; decide +kernel
-- END walks_0

-- BEGIN walks_1
/-- square-grid walks of 1 steps that never revisit a point (OEIS A001411). -/
theorem walks_1 :
    selfAvoiding 1 = 4 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 1 (by norm_num)]; decide +kernel
-- END walks_1

-- BEGIN walks_2
/-- square-grid walks of 2 steps that never revisit a point (OEIS A001411). -/
theorem walks_2 :
    selfAvoiding 2 = 12 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 2 (by norm_num)]; decide +kernel
-- END walks_2

-- BEGIN walks_3
/-- square-grid walks of 3 steps that never revisit a point (OEIS A001411). -/
theorem walks_3 :
    selfAvoiding 3 = 36 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 3 (by norm_num)]; decide +kernel
-- END walks_3

-- BEGIN walks_4
/-- square-grid walks of 4 steps that never revisit a point (OEIS A001411). -/
theorem walks_4 :
    selfAvoiding 4 = 100 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 4 (by norm_num)]; decide +kernel
-- END walks_4

-- BEGIN walks_5
/-- square-grid walks of 5 steps that never revisit a point (OEIS A001411). -/
theorem walks_5 :
    selfAvoiding 5 = 284 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 5 (by norm_num)]; decide +kernel
-- END walks_5

-- BEGIN walks_6
/-- square-grid walks of 6 steps that never revisit a point (OEIS A001411). -/
theorem walks_6 :
    selfAvoiding 6 = 780 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 6 (by norm_num)]; decide +kernel
-- END walks_6

-- BEGIN walks_7
/-- square-grid walks of 7 steps that never revisit a point (OEIS A001411). -/
theorem walks_7 :
    selfAvoiding 7 = 2172 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 7 (by norm_num)]; decide +kernel
-- END walks_7

-- BEGIN walks_8
/-- square-grid walks of 8 steps that never revisit a point (OEIS A001411). -/
theorem walks_8 :
    selfAvoiding 8 = 5916 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 8 (by norm_num)]; decide +kernel
-- END walks_8

-- BEGIN walks_9
/-- square-grid walks of 9 steps that never revisit a point (OEIS A001411). -/
theorem walks_9 :
    selfAvoiding 9 = 16268 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 9 (by norm_num)]; decide +kernel
-- END walks_9

-- BEGIN walks_10
/-- square-grid walks of 10 steps that never revisit a point (OEIS A001411). -/
theorem walks_10 :
    selfAvoiding 10 = 44100 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 10 (by norm_num)]; decide +kernel
-- END walks_10

-- BEGIN walks_11
/-- square-grid walks of 11 steps that never revisit a point (OEIS A001411). -/
theorem walks_11 :
    selfAvoiding 11 = 120292 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 11 (by norm_num)]; decide +kernel
-- END walks_11

-- BEGIN walks_12
/-- square-grid walks of 12 steps that never revisit a point (OEIS A001411). -/
theorem walks_12 :
    selfAvoiding 12 = 324932 := by
  set_option maxRecDepth 100000 in
  rw [WalkCount.selfAvoiding_eq 12 (by norm_num)]; decide +kernel
-- END walks_12

-- BEGIN graph_amcs_n13_k5_2026_10_15T01_53_33_663Z
/-- saved graph amcs-n13-k5-2026-10-15T01-53-33-663Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_amcs_n13_k5_2026_10_15T01_53_33_663Z :
    TriangleFree 13 graph_amcs_n13_k5_2026_10_15T01_53_33_663Z_edges ∧ NoStrangers 13 5 graph_amcs_n13_k5_2026_10_15T01_53_33_663Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_amcs_n13_k5_2026_10_15T01_53_33_663Z
-- END graph_amcs_n13_k5_2026_10_15T01_53_33_663Z

-- BEGIN graph_amcs_n13_k5_2026_10_15T01_54_36_788Z
/-- saved graph amcs-n13-k5-2026-10-15T01-54-36-788Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_amcs_n13_k5_2026_10_15T01_54_36_788Z :
    TriangleFree 13 graph_amcs_n13_k5_2026_10_15T01_54_36_788Z_edges ∧ NoStrangers 13 5 graph_amcs_n13_k5_2026_10_15T01_54_36_788Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_amcs_n13_k5_2026_10_15T01_54_36_788Z
-- END graph_amcs_n13_k5_2026_10_15T01_54_36_788Z

-- BEGIN graph_amcs_n17_k6_2026_10_15T01_53_33_852Z
/-- saved graph amcs-n17-k6-2026-10-15T01-53-33-852Z.json: 17 vertices, no triangle and no 6 strangers. -/
theorem graph_amcs_n17_k6_2026_10_15T01_53_33_852Z :
    TriangleFree 17 graph_amcs_n17_k6_2026_10_15T01_53_33_852Z_edges ∧ NoStrangers 17 6 graph_amcs_n17_k6_2026_10_15T01_53_33_852Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_amcs_n17_k6_2026_10_15T01_53_33_852Z
-- END graph_amcs_n17_k6_2026_10_15T01_53_33_852Z

-- BEGIN graph_amcs_n17_k6_2026_10_15T01_54_36_944Z
/-- saved graph amcs-n17-k6-2026-10-15T01-54-36-944Z.json: 17 vertices, no triangle and no 6 strangers. -/
theorem graph_amcs_n17_k6_2026_10_15T01_54_36_944Z :
    TriangleFree 17 graph_amcs_n17_k6_2026_10_15T01_54_36_944Z_edges ∧ NoStrangers 17 6 graph_amcs_n17_k6_2026_10_15T01_54_36_944Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_amcs_n17_k6_2026_10_15T01_54_36_944Z
-- END graph_amcs_n17_k6_2026_10_15T01_54_36_944Z

-- BEGIN graph_amcs_n22_k7_2026_10_15T01_54_54_955Z
/-- saved graph amcs-n22-k7-2026-10-15T01-54-54-955Z.json: 22 vertices, no triangle and no 7 strangers. -/
theorem graph_amcs_n22_k7_2026_10_15T01_54_54_955Z :
    TriangleFree 22 graph_amcs_n22_k7_2026_10_15T01_54_54_955Z_edges ∧ NoStrangers 22 7 graph_amcs_n22_k7_2026_10_15T01_54_54_955Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_amcs_n22_k7_2026_10_15T01_54_54_955Z
-- END graph_amcs_n22_k7_2026_10_15T01_54_54_955Z

-- BEGIN graph_amcs_n8_k4_2026_10_15T01_53_33_552Z
/-- saved graph amcs-n8-k4-2026-10-15T01-53-33-552Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_amcs_n8_k4_2026_10_15T01_53_33_552Z :
    TriangleFree 8 graph_amcs_n8_k4_2026_10_15T01_53_33_552Z_edges ∧ NoStrangers 8 4 graph_amcs_n8_k4_2026_10_15T01_53_33_552Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_amcs_n8_k4_2026_10_15T01_53_33_552Z
-- END graph_amcs_n8_k4_2026_10_15T01_53_33_552Z

-- BEGIN graph_amcs_n8_k4_2026_10_15T01_54_36_642Z
/-- saved graph amcs-n8-k4-2026-10-15T01-54-36-642Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_amcs_n8_k4_2026_10_15T01_54_36_642Z :
    TriangleFree 8 graph_amcs_n8_k4_2026_10_15T01_54_36_642Z_edges ∧ NoStrangers 8 4 graph_amcs_n8_k4_2026_10_15T01_54_36_642Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_amcs_n8_k4_2026_10_15T01_54_36_642Z
-- END graph_amcs_n8_k4_2026_10_15T01_54_36_642Z

-- BEGIN graph_anneal_n13_k5_2026_10_14T13_56_23_903Z
/-- saved graph anneal-n13-k5-2026-10-14T13-56-23-903Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_anneal_n13_k5_2026_10_14T13_56_23_903Z :
    TriangleFree 13 graph_anneal_n13_k5_2026_10_14T13_56_23_903Z_edges ∧ NoStrangers 13 5 graph_anneal_n13_k5_2026_10_14T13_56_23_903Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T13_56_23_903Z
-- END graph_anneal_n13_k5_2026_10_14T13_56_23_903Z

-- BEGIN graph_anneal_n13_k5_2026_10_14T14_06_17_873Z
/-- saved graph anneal-n13-k5-2026-10-14T14-06-17-873Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_anneal_n13_k5_2026_10_14T14_06_17_873Z :
    TriangleFree 13 graph_anneal_n13_k5_2026_10_14T14_06_17_873Z_edges ∧ NoStrangers 13 5 graph_anneal_n13_k5_2026_10_14T14_06_17_873Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T14_06_17_873Z
-- END graph_anneal_n13_k5_2026_10_14T14_06_17_873Z

-- BEGIN graph_anneal_n13_k5_2026_10_14T15_10_04_875Z
/-- saved graph anneal-n13-k5-2026-10-14T15-10-04-875Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_anneal_n13_k5_2026_10_14T15_10_04_875Z :
    TriangleFree 13 graph_anneal_n13_k5_2026_10_14T15_10_04_875Z_edges ∧ NoStrangers 13 5 graph_anneal_n13_k5_2026_10_14T15_10_04_875Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T15_10_04_875Z
-- END graph_anneal_n13_k5_2026_10_14T15_10_04_875Z

-- BEGIN graph_anneal_n13_k5_2026_10_14T15_11_12_007Z
/-- saved graph anneal-n13-k5-2026-10-14T15-11-12-007Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_anneal_n13_k5_2026_10_14T15_11_12_007Z :
    TriangleFree 13 graph_anneal_n13_k5_2026_10_14T15_11_12_007Z_edges ∧ NoStrangers 13 5 graph_anneal_n13_k5_2026_10_14T15_11_12_007Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T15_11_12_007Z
-- END graph_anneal_n13_k5_2026_10_14T15_11_12_007Z

-- BEGIN graph_anneal_n13_k5_2026_10_14T15_23_48_940Z
/-- saved graph anneal-n13-k5-2026-10-14T15-23-48-940Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_anneal_n13_k5_2026_10_14T15_23_48_940Z :
    TriangleFree 13 graph_anneal_n13_k5_2026_10_14T15_23_48_940Z_edges ∧ NoStrangers 13 5 graph_anneal_n13_k5_2026_10_14T15_23_48_940Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_anneal_n13_k5_2026_10_14T15_23_48_940Z
-- END graph_anneal_n13_k5_2026_10_14T15_23_48_940Z

-- BEGIN graph_circulant_n13_k5_2026_10_14T13_56_23_520Z
/-- saved graph circulant-n13-k5-2026-10-14T13-56-23-520Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_circulant_n13_k5_2026_10_14T13_56_23_520Z :
    TriangleFree 13 graph_circulant_n13_k5_2026_10_14T13_56_23_520Z_edges ∧ NoStrangers 13 5 graph_circulant_n13_k5_2026_10_14T13_56_23_520Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T13_56_23_520Z
-- END graph_circulant_n13_k5_2026_10_14T13_56_23_520Z

-- BEGIN graph_circulant_n13_k5_2026_10_14T14_06_20_071Z
/-- saved graph circulant-n13-k5-2026-10-14T14-06-20-071Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_circulant_n13_k5_2026_10_14T14_06_20_071Z :
    TriangleFree 13 graph_circulant_n13_k5_2026_10_14T14_06_20_071Z_edges ∧ NoStrangers 13 5 graph_circulant_n13_k5_2026_10_14T14_06_20_071Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T14_06_20_071Z
-- END graph_circulant_n13_k5_2026_10_14T14_06_20_071Z

-- BEGIN graph_circulant_n13_k5_2026_10_14T15_10_07_045Z
/-- saved graph circulant-n13-k5-2026-10-14T15-10-07-045Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_circulant_n13_k5_2026_10_14T15_10_07_045Z :
    TriangleFree 13 graph_circulant_n13_k5_2026_10_14T15_10_07_045Z_edges ∧ NoStrangers 13 5 graph_circulant_n13_k5_2026_10_14T15_10_07_045Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T15_10_07_045Z
-- END graph_circulant_n13_k5_2026_10_14T15_10_07_045Z

-- BEGIN graph_circulant_n13_k5_2026_10_14T15_11_14_178Z
/-- saved graph circulant-n13-k5-2026-10-14T15-11-14-178Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_circulant_n13_k5_2026_10_14T15_11_14_178Z :
    TriangleFree 13 graph_circulant_n13_k5_2026_10_14T15_11_14_178Z_edges ∧ NoStrangers 13 5 graph_circulant_n13_k5_2026_10_14T15_11_14_178Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T15_11_14_178Z
-- END graph_circulant_n13_k5_2026_10_14T15_11_14_178Z

-- BEGIN graph_circulant_n13_k5_2026_10_14T15_23_51_122Z
/-- saved graph circulant-n13-k5-2026-10-14T15-23-51-122Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_circulant_n13_k5_2026_10_14T15_23_51_122Z :
    TriangleFree 13 graph_circulant_n13_k5_2026_10_14T15_23_51_122Z_edges ∧ NoStrangers 13 5 graph_circulant_n13_k5_2026_10_14T15_23_51_122Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n13_k5_2026_10_14T15_23_51_122Z
-- END graph_circulant_n13_k5_2026_10_14T15_23_51_122Z

-- BEGIN graph_circulant_n35_k9_2026_10_14T13_56_47_249Z
/-- saved graph circulant-n35-k9-2026-10-14T13-56-47-249Z.json: 35 vertices, no triangle and no 9 strangers. -/
theorem graph_circulant_n35_k9_2026_10_14T13_56_47_249Z :
    TriangleFree 35 graph_circulant_n35_k9_2026_10_14T13_56_47_249Z_edges ∧ NoStrangers 35 9 graph_circulant_n35_k9_2026_10_14T13_56_47_249Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n35_k9_2026_10_14T13_56_47_249Z

-- END graph_circulant_n35_k9_2026_10_14T13_56_47_249Z

-- BEGIN graph_circulant_n38_k10_2026_10_14T13_56_49_410Z
/-- saved graph circulant-n38-k10-2026-10-14T13-56-49-410Z.json: 38 vertices, no triangle and no 10 strangers. -/
theorem graph_circulant_n38_k10_2026_10_14T13_56_49_410Z :
    TriangleFree 38 graph_circulant_n38_k10_2026_10_14T13_56_49_410Z_edges ∧ NoStrangers 38 10 graph_circulant_n38_k10_2026_10_14T13_56_49_410Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n38_k10_2026_10_14T13_56_49_410Z

-- END graph_circulant_n38_k10_2026_10_14T13_56_49_410Z

-- BEGIN graph_circulant_n8_k4_2026_10_14T13_56_23_372Z
/-- saved graph circulant-n8-k4-2026-10-14T13-56-23-372Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_circulant_n8_k4_2026_10_14T13_56_23_372Z :
    TriangleFree 8 graph_circulant_n8_k4_2026_10_14T13_56_23_372Z_edges ∧ NoStrangers 8 4 graph_circulant_n8_k4_2026_10_14T13_56_23_372Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T13_56_23_372Z
-- END graph_circulant_n8_k4_2026_10_14T13_56_23_372Z

-- BEGIN graph_circulant_n8_k4_2026_10_14T14_06_20_015Z
/-- saved graph circulant-n8-k4-2026-10-14T14-06-20-015Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_circulant_n8_k4_2026_10_14T14_06_20_015Z :
    TriangleFree 8 graph_circulant_n8_k4_2026_10_14T14_06_20_015Z_edges ∧ NoStrangers 8 4 graph_circulant_n8_k4_2026_10_14T14_06_20_015Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T14_06_20_015Z
-- END graph_circulant_n8_k4_2026_10_14T14_06_20_015Z

-- BEGIN graph_circulant_n8_k4_2026_10_14T15_10_06_995Z
/-- saved graph circulant-n8-k4-2026-10-14T15-10-06-995Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_circulant_n8_k4_2026_10_14T15_10_06_995Z :
    TriangleFree 8 graph_circulant_n8_k4_2026_10_14T15_10_06_995Z_edges ∧ NoStrangers 8 4 graph_circulant_n8_k4_2026_10_14T15_10_06_995Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T15_10_06_995Z
-- END graph_circulant_n8_k4_2026_10_14T15_10_06_995Z

-- BEGIN graph_circulant_n8_k4_2026_10_14T15_11_14_131Z
/-- saved graph circulant-n8-k4-2026-10-14T15-11-14-131Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_circulant_n8_k4_2026_10_14T15_11_14_131Z :
    TriangleFree 8 graph_circulant_n8_k4_2026_10_14T15_11_14_131Z_edges ∧ NoStrangers 8 4 graph_circulant_n8_k4_2026_10_14T15_11_14_131Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T15_11_14_131Z
-- END graph_circulant_n8_k4_2026_10_14T15_11_14_131Z

-- BEGIN graph_circulant_n8_k4_2026_10_14T15_23_51_067Z
/-- saved graph circulant-n8-k4-2026-10-14T15-23-51-067Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_circulant_n8_k4_2026_10_14T15_23_51_067Z :
    TriangleFree 8 graph_circulant_n8_k4_2026_10_14T15_23_51_067Z_edges ∧ NoStrangers 8 4 graph_circulant_n8_k4_2026_10_14T15_23_51_067Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_circulant_n8_k4_2026_10_14T15_23_51_067Z
-- END graph_circulant_n8_k4_2026_10_14T15_23_51_067Z

-- BEGIN graph_exoo_n39_k10
/-- saved graph exoo-n39-k10.json: 39 vertices, no triangle and no 10 strangers. -/
theorem graph_exoo_n39_k10 :
    TriangleFree 39 graph_exoo_n39_k10_edges ∧ NoStrangers 39 10 graph_exoo_n39_k10_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_exoo_n39_k10

-- END graph_exoo_n39_k10

-- BEGIN graph_grown_n13_k5_1791990648209
/-- saved graph grown-n13-k5-1791990648209.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_grown_n13_k5_1791990648209 :
    TriangleFree 13 graph_grown_n13_k5_1791990648209_edges ∧ NoStrangers 13 5 graph_grown_n13_k5_1791990648209_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_grown_n13_k5_1791990648209
-- END graph_grown_n13_k5_1791990648209

-- BEGIN graph_grown_n36_k10_1791990649104
/-- saved graph grown-n36-k10-1791990649104.json: 36 vertices, no triangle and no 10 strangers. -/
theorem graph_grown_n36_k10_1791990649104 :
    TriangleFree 36 graph_grown_n36_k10_1791990649104_edges ∧ NoStrangers 36 10 graph_grown_n36_k10_1791990649104_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_grown_n36_k10_1791990649104

-- END graph_grown_n36_k10_1791990649104

-- BEGIN graph_ladder_n13_k5_2026_10_14T13_57_09_399Z
/-- saved graph ladder-n13-k5-2026-10-14T13-57-09-399Z.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_ladder_n13_k5_2026_10_14T13_57_09_399Z :
    TriangleFree 13 graph_ladder_n13_k5_2026_10_14T13_57_09_399Z_edges ∧ NoStrangers 13 5 graph_ladder_n13_k5_2026_10_14T13_57_09_399Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_ladder_n13_k5_2026_10_14T13_57_09_399Z
-- END graph_ladder_n13_k5_2026_10_14T13_57_09_399Z

-- BEGIN graph_ladder_n17_k6_2026_10_14T13_57_09_484Z
/-- saved graph ladder-n17-k6-2026-10-14T13-57-09-484Z.json: 17 vertices, no triangle and no 6 strangers. -/
theorem graph_ladder_n17_k6_2026_10_14T13_57_09_484Z :
    TriangleFree 17 graph_ladder_n17_k6_2026_10_14T13_57_09_484Z_edges ∧ NoStrangers 17 6 graph_ladder_n17_k6_2026_10_14T13_57_09_484Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_ladder_n17_k6_2026_10_14T13_57_09_484Z
-- END graph_ladder_n17_k6_2026_10_14T13_57_09_484Z

-- BEGIN graph_ladder_n22_k7_2026_10_14T13_57_09_620Z
/-- saved graph ladder-n22-k7-2026-10-14T13-57-09-620Z.json: 22 vertices, no triangle and no 7 strangers. -/
theorem graph_ladder_n22_k7_2026_10_14T13_57_09_620Z :
    TriangleFree 22 graph_ladder_n22_k7_2026_10_14T13_57_09_620Z_edges ∧ NoStrangers 22 7 graph_ladder_n22_k7_2026_10_14T13_57_09_620Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_ladder_n22_k7_2026_10_14T13_57_09_620Z
-- END graph_ladder_n22_k7_2026_10_14T13_57_09_620Z

-- BEGIN graph_ladder_n27_k8_2026_10_14T13_57_09_890Z
/-- saved graph ladder-n27-k8-2026-10-14T13-57-09-890Z.json: 27 vertices, no triangle and no 8 strangers. -/
theorem graph_ladder_n27_k8_2026_10_14T13_57_09_890Z :
    TriangleFree 27 graph_ladder_n27_k8_2026_10_14T13_57_09_890Z_edges ∧ NoStrangers 27 8 graph_ladder_n27_k8_2026_10_14T13_57_09_890Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_ladder_n27_k8_2026_10_14T13_57_09_890Z
-- END graph_ladder_n27_k8_2026_10_14T13_57_09_890Z

-- BEGIN graph_ladder_n8_k4_2026_10_14T13_57_09_336Z
/-- saved graph ladder-n8-k4-2026-10-14T13-57-09-336Z.json: 8 vertices, no triangle and no 4 strangers. -/
theorem graph_ladder_n8_k4_2026_10_14T13_57_09_336Z :
    TriangleFree 8 graph_ladder_n8_k4_2026_10_14T13_57_09_336Z_edges ∧ NoStrangers 8 4 graph_ladder_n8_k4_2026_10_14T13_57_09_336Z_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_ladder_n8_k4_2026_10_14T13_57_09_336Z
-- END graph_ladder_n8_k4_2026_10_14T13_57_09_336Z

-- BEGIN graph_test_n12_k5_plus1
/-- saved graph test-n12-k5-plus1.json: 13 vertices, no triangle and no 5 strangers. -/
theorem graph_test_n12_k5_plus1 :
    TriangleFree 13 graph_test_n12_k5_plus1_edges ∧ NoStrangers 13 5 graph_test_n12_k5_plus1_edges := by
  exact GraphCheck.check_sound GraphCheck.cert_graph_test_n12_k5_plus1
-- END graph_test_n12_k5_plus1

end TowerBatch
