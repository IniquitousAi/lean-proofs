# HHH algebrization release: Aaronson-Wigderson 2009 Theorem 5.3 in Lean 4

A machine-checked formalization of the known 2009 Aaronson-Wigderson algebrization barrier
(S. Aaronson, A. Wigderson, "Algebrization: A New Barrier in Complexity Theory", STOC 2008; ACM TOCT 2009).
Not new math, not a resolution of P vs NP.

## Contents
- `HHHAlg.lean`: the whole development in one file (imports Mathlib + Relativization).
- `src/`: the same content as the original pieces (AW.lean, AW53.lean, AWB.lean, BridgeTail.lean, BridgeEnc.lean).
- `Axioms.lean`: `#print axioms` for the main theorems.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: upstream BGS repo files at commit
  2d9d84792344a53422e03b888aaa708b7d6d47f6 (Lean v4.31.0, Mathlib rev fabf563a7c95a166b8d7b6efca11c8b4dc9d911f),
  plus one `[[lean_lib]] HHHAlg` entry.
- `check.sh`: clones the BGS repo at that commit, overlays these files, builds, counts sorry, prints axioms.
  `UP=` picks a clone source; `PKGS=` symlinks an existing `.lake/packages` (no new Mathlib download).
- `check_run.log`: a verification run (`UP=<local BGS checkout> PKGS=<its .lake/packages> ./check.sh`):
  build OK, sorry count 0, all axioms [propext, Classical.choice, Quot.sound]. [checked]

## Main Lean statements [checked]

```lean
-- concrete encoding, all finite fields GaloisField p k (GFIdx := Σ p : {p // p.Prime}, ℕ)
theorem HHH.Bridge.aw_tm_separation_galois :
  ∃ (A : (m : ℕ) → (Fin m → Bool) → Bool) (P : ∀ x : GFIdx, (m : ℕ) → MvPolynomial (Fin m) (GF x)) (B : Oracle),
    (∀ x m, (∀ j, degreeOf j (P x m) ≤ 2) ∧ ∀ z, eval (HHH.AW.bool z) (P x m) = if A m z then 1 else 0) ∧
    (∀ s, s ∈ B ↔ ∃ m z, A m z = true ∧ s = List.ofFn z ++ List.replicate m false) ∧
    InNP B (fin_encoding_string Bool) (sepLang B) ∧
    ¬ InP (Aenc gfEnc (mOrc P)) (fin_encoding_string Bool) (sepLang B)

theorem HHH.Bridge.aw_tm_separation (E : Enc Fk) : ... -- same, any family of fields, any encoding E

theorem HHH.Bridge.gfDec_encode (x : GFIdx) (m : ℕ) (y : Fin m → GF x) (i : ℕ) :
  gfDec (gfEncode x m y i) = some (⟨x, m, fun j => if h : j < m then y ⟨j, h⟩ else 0⟩, i)
theorem HHH.Bridge.mem_Aenc_gf (O) (x m y i) :
  gfEncode x m y i ∈ Aenc gfEnc O ↔ (code x (O x m (fun j => if h : j < m then y ⟨j, h⟩ else 0))).testBit i = true
theorem HHH.Bridge.bits_determine (x : GFIdx) (a b : GF x)
  (h : ∀ i, gfEnc.bit ⟨x, a⟩ i = gfEnc.bit ⟨x, b⟩ i) : a = b
theorem HHH.Bridge.finite_field_iso_galois (K) [Field K] [Fintype K] : ∃ x : GFIdx, Nonempty (K ≃+* GF x)

-- whole-field-element answer model (query machines, answers are elements of Fk k)
theorem HHH.AWB.theorem_5_3_spread (M : ℕ → QMM Fk) (N) (hN : ∀ i n, N i ≤ n → (M i).time n < 2 ^ n) :
  ∃ nA A P, (multiquadratic extension of A over every field) ∧ (∀ j i, j < i → 2 * nA j < nA i) ∧
    (∀ m z, A m z = true → ∃ j, m = nA j) ∧
    ∀ i, ((M i).out (nA i) (mrun (M i) (nA i) (mOrc P) ((M i).time (nA i))) = true ↔ ¬ ∃ z, A (nA i) z = true)
```
Supporting (AW.lean / AW53.lean, earlier rounds, [checked]): lemma_4_2, lemma_4_3, theorem_4_4,
lemma_4_5_good (all fields at once), one_query_decides (why multilinear fails), theorem_5_3_query.

Encoding gfEnc: a query string is wr p ++ wr k ++ wr m ++ wr(code y_0) ++ ... ++ wr(code y_{m-1}) ++ wr i,
wr = self-delimiting binary (pairs (1,bit), LSB first, then 0; length 2 log n + 1). Answer bit i =
bit i of the element's index under Finite.equivFin. Strings that fail to parse (or p not prime) are not in the oracle.

## Matches the paper [reasoned, from the statements above]
- Thm 5.3 (NP^A ⊄ P^Ã) with Ã a multiquadratic (deg ≤ 2 per variable) extension of A over every finite field
  simultaneously; L = "some length-n string is in A" (here as BGS sepLang B on 0^n).
- Lemma 4.5 adversary (2^n - t good points), Lemma 4.3/Thm 4.4 deterministic query lower bound.
- Every finite field is covered (finite_field_iso_galois).
- Diagonalization over all poly-time oracle TMs (BGS dEnum / exists_dcode_decides).

## Differs [reasoned]
- Machine model: BGS multi-stack OracleFinTM2 with one Boolean query per step, not the paper's multitape TM.
- Answer convention: in the TM theorem Ã is accessed bitwise (Aenc: one bit of the element per query).
  The paper's one-element-per-query convention is exactly the QMM model (theorem_5_3_spread, instantiate Fk := GF),
  where any (not just TM) machine gets whole field elements and the time bound counts queries; that is a
  stronger adversary. bits_determine + mem_Aenc_gf show the bit oracle carries exactly the element's code;
  a TM can fetch an element in O(log|F|) bit queries, so poly-time classes agree up to poly factors [reasoned, not formalized].
- No TM model with field-valued oracle tapes exists in BGS, so "TM + whole-element answers" is not a separate Lean statement.
- Only extension degree 2 per variable (multiquadratic), fields only (no integer extensions), deterministic P only
  (no BPP/RP/communication-complexity parts of the paper). Language uses inputs 0^n (BGS) not 1^n.
- NP side oracle is the Boolean B; P side oracle is Aenc(Ã), which also encodes A since Ã extends it.

## Prior art (search 2026-10-30) [measured: web search, Oct 30; no hits is a guess, not proof of absence]
- No Lean/Isabelle/Coq formalization of algebrization found (web search: "algebrization Aaronson Wigderson
  formalization Lean OR Isabelle OR Coq"; only hit was unrelated coq-wigderson graph coloring).
- Related: Impagliazzo-Kabanets-Kolokolova "An axiomatic approach to algebrization" (STOC 2009) is a paper logic, not a proof-assistant development.
- Relativization: JoshuaTan42/lean-relativization-bgs (Lean BGS; reused here, commit 2d9d847);
  tannerduve/computability (Lean oracle computability, Turing degrees; no complexity classes).
- Natural proofs: crabsatellite repo (cloned in bgs/np, not built).
- [guess] absence of results is not proof of absence; private/unindexed work may exist.
