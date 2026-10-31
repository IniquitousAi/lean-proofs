namespace HHH.Bridge
open Relativization Turing HHH.AW HHH.AWB MvPolynomial Millennium
open scoped Classical

/-! Round 7: a concrete standard encoding for all finite fields GaloisField p k. -/

/-- Self-delimiting binary code of n: pairs (true, bit) LSB first, then a single false. -/
def wr (n : ℕ) : List Bool :=
  if h : n = 0 then [false] else true :: n.testBit 0 :: wr (n / 2)
decreasing_by omega

def readNum : List Bool → Option (ℕ × List Bool)
  | false :: r => some (0, r)
  | true :: b :: r => (readNum r).map fun p => (Nat.bit b p.1, p.2)
  | _ => none

theorem readNum_wr (n : ℕ) (r : List Bool) : readNum (wr n ++ r) = some (n, r) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [wr]
    split_ifs with h
    · subst h; rfl
    · simp only [List.cons_append, readNum]
      rw [ih (n / 2) (by omega)]
      have := Nat.bit_testBit_zero_shiftRight_one n
      rw [Nat.shiftRight_one] at this
      simp only [Option.map_some, this]

def readList : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, r => some ([], r)
  | m + 1, r => (readNum r).bind fun p => (readList m p.2).map fun q => (p.1 :: q.1, q.2)

theorem readList_wr (l : List ℕ) (r : List Bool) :
    readList l.length ((l.map wr).flatten ++ r) = some (l, r) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, readList,
      readNum_wr, Option.bind_some, ih, Option.map_some]

/-- field element <-> index in Fin (card) -/
noncomputable def code (x : GFIdx) (v : GF x) : ℕ := (Finite.equivFin (GF x) v).val
noncomputable def elt (x : GFIdx) (e : ℕ) : GF x :=
  if h : e < Nat.card (GF x) then (Finite.equivFin (GF x)).symm ⟨e, h⟩ else 0

theorem elt_code (x : GFIdx) (v : GF x) : elt x (code x v) = v := by
  unfold elt code
  rw [dif_pos (Finite.equivFin (GF x) v).isLt]
  simp

theorem code_injective (x : GFIdx) : Function.Injective (code x) := fun a b h => by
  rw [← elt_code x a, h, elt_code]

/-- the field-query point, read from a list of element codes -/
noncomputable def ptOf (x : GFIdx) (m : ℕ) (es : List ℕ) : ℕ → GF x :=
  fun j => if j < m then elt x (es.getD j 0) else 0

/-- The decoder: p, k, m, then m element codes, then the bit index i (all self-delimiting). -/
noncomputable def gfDec (s : List Bool) : Option (MQ GF × ℕ) :=
  match readNum s with
  | none => none
  | some (p, s1) =>
  match readNum s1 with
  | none => none
  | some (k, s2) =>
  match readNum s2 with
  | none => none
  | some (m, s3) =>
  match readList m s3 with
  | none => none
  | some (es, s4) =>
  match readNum s4 with
  | none => none
  | some (i, _) =>
    if hp : p.Prime then some (⟨⟨⟨p, hp⟩, k⟩, m, ptOf ⟨⟨p, hp⟩, k⟩ m es⟩, i) else none

/-- The concrete standard encoding: bit i of an answer is bit i of its element code. -/
noncomputable def gfEnc : Enc GF where
  dec := gfDec
  bit a i := (code a.1 a.2).testBit i
  dummy := ⟨⟨⟨2, Nat.prime_two⟩, 1⟩, 0, fun _ => 0⟩

/-- The encoder of the query "bit i of Ã_{m,GF x}(y)". -/
noncomputable def gfEncode (x : GFIdx) (m : ℕ) (y : Fin m → GF x) (i : ℕ) : List Bool :=
  wr x.1.1 ++ wr x.2 ++ wr m ++ ((List.ofFn fun j => code x (y j)).map wr).flatten ++ wr i

/-- Round trip: every field query and bit index has a code, decoded exactly. -/
theorem gfDec_encode (x : GFIdx) (m : ℕ) (y : Fin m → GF x) (i : ℕ) :
    gfDec (gfEncode x m y i) =
      some (⟨x, m, fun j => if h : j < m then y ⟨j, h⟩ else 0⟩, i) := by
  have hl : (List.ofFn fun j => code x (y j)).length = m := List.length_ofFn
  have hr := readList_wr (List.ofFn fun j => code x (y j)) (wr i)
  rw [hl] at hr
  unfold gfDec gfEncode
  simp only [List.append_assoc, readNum_wr, hr, List.append_nil]
  have hi := readNum_wr i []
  rw [List.append_nil] at hi
  rw [hi]
  simp only [dif_pos x.1.2]
  congr
  funext j
  unfold ptOf
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by rw [hl]; exact h), List.getElem_ofFn, elt_code]
  · rfl

/-- Bit answers determine the whole field element (relates Aenc to whole-element answers). -/
theorem bits_determine (x : GFIdx) (a b : GF x)
    (h : ∀ i, gfEnc.bit ⟨x, a⟩ i = gfEnc.bit ⟨x, b⟩ i) : a = b :=
  code_injective x (Nat.eq_of_testBit_eq h)

/-- AW Theorem 5.3 in the BGS TM model, concrete encoding, all finite fields GaloisField p k:
NP^B not contained in P^{Ã}, Ã the bit-encoded multiquadratic extensions over every GF(p^k). -/
theorem aw_tm_separation_galois :
    ∃ (A : (m : ℕ) → (Fin m → Bool) → Bool) (P : ∀ x : GFIdx, (m : ℕ) → MvPolynomial (Fin m) (GF x))
      (B : Oracle),
      (∀ x m, (∀ j, degreeOf j (P x m) ≤ 2) ∧
        ∀ z, eval (HHH.AW.bool z) (P x m) = if A m z then 1 else 0) ∧
      (∀ s, s ∈ B ↔ ∃ m z, A m z = true ∧ s = List.ofFn z ++ List.replicate m false) ∧
      InNP B (fin_encoding_string Bool) (sepLang B) ∧
      ¬ InP (Aenc gfEnc (mOrc P)) (fin_encoding_string Bool) (sepLang B) :=
  aw_tm_separation gfEnc

/-- The concrete oracle: gfEncode x m y i is in it iff bit i of the code of Ã_{m,x}(y) is 1. -/
theorem mem_Aenc_gf (O : MOrc GF) (x : GFIdx) (m : ℕ) (y : Fin m → GF x) (i : ℕ) :
    gfEncode x m y i ∈ Aenc gfEnc O ↔
      (code x (O x m (fun j => if h : j < m then y ⟨j, h⟩ else 0))).testBit i = true := by
  unfold Aenc bitAns qOf
  simp only [Set.mem_setOf_eq]
  rw [show gfEnc.dec = gfDec from rfl, gfDec_encode]
  rfl

end HHH.Bridge
