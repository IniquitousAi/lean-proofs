namespace HHH.Bridge
open Relativization Turing HHH.AW HHH.AWB MvPolynomial Millennium
open scoped Classical

abbrev GFIdx := Σ _p : {p : ℕ // p.Prime}, ℕ
noncomputable abbrev GF (x : GFIdx) : Type := @GaloisField x.1.1 ⟨x.1.2⟩ x.2
noncomputable instance (x : GFIdx) : Field (GF x) := by
  letI : Fact x.1.1.Prime := ⟨x.1.2⟩; unfold GF; infer_instance

/-- Every finite field is isomorphic to some GaloisField p n (closes the GF-index gap). -/
theorem finite_field_iso_galois (K : Type*) [Field K] [Fintype K] :
    ∃ x : GFIdx, Nonempty (K ≃+* GF x) := by
  obtain ⟨p, hc⟩ := CharP.exists K
  obtain ⟨n, hp, hK⟩ := FiniteField.card K p
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fintype (GaloisField p n) := Fintype.ofFinite _
  refine ⟨⟨⟨p, hp⟩, n⟩, ⟨FiniteField.ringEquivOfCardEq ?_⟩⟩
  rw [hK, ← Nat.card_eq_fintype_card, GaloisField.card p n n.ne_zero]

variable {κ : Type} {Fk : κ → Type} [∀ k, Field (Fk k)]

/-- Step 1: an encoding of field queries as bit strings, left abstract (any scheme works):
`dec s = some (q, i)` means "string s asks for bit i of the answer to field query q". -/
structure Enc (Fk : κ → Type) [∀ k, Field (Fk k)] where
  dec : List Bool → Option (MQ Fk × ℕ)
  bit : MA Fk → ℕ → Bool
  dummy : MQ Fk

def qOf (E : Enc Fk) (s : List Bool) : MQ Fk :=
  match E.dec s with | some (q, _) => q | none => E.dummy

def bitAns (E : Enc Fk) (s : List Bool) (a : MA Fk) : Bool :=
  match E.dec s with | some (_, i) => E.bit a i | none => false

/-- The Boolean oracle a BGS machine sees: bit-encoding of the field oracle O. -/
def Aenc (E : Enc Fk) (O : MOrc Fk) : Oracle := {s | bitAns E s (mans Fk O (qOf E s)) = true}

variable (E : Enc Fk) (tm : OracleFinTM2)

noncomputable def stepW (b : Bool) (c : tm.Cfg) : Option tm.Cfg := TM2.step (fun l => tm.m l b) c

lemma step_eq (A : Oracle) (c : tm.Cfg) : tm.step A c = stepW tm (decide (tm.query c ∈ A)) c := rfl

/-- Replay a TM from the list of field answers seen so far. -/
noncomputable def replay (inp : List (tm.Γ tm.k₀)) (as : List (MA Fk)) : Option tm.Cfg :=
  as.foldl (fun oc a => oc.bind (fun c => stepW tm (bitAns E (tm.query c) a) c)) (some (tm.initList inp))

lemma replay_snoc (inp : List (tm.Γ tm.k₀)) (as : List (MA Fk)) (a : MA Fk) :
    replay E tm inp (as ++ [a]) = (replay E tm inp as).bind (fun c => stepW tm (bitAns E (tm.query c) a) c) := by
  simp [replay, List.foldl_append]

/-- Step 2: the oracle TM as a query machine (one field query per TM step). -/
noncomputable def simQ (inp : ℕ → List (tm.Γ tm.k₀)) (acc : List (tm.Γ tm.k₁)) (T : ℕ → ℕ) : QMM Fk where
  time := T
  next n as := match replay E tm (inp n) as with | some c => qOf E (tm.query c) | none => E.dummy
  out n as := decide (∃ j ≤ as.length, replay E tm (inp n) (as.take j) = some (tm.haltList acc))

lemma mrun_length (M : QMM Fk) (n : ℕ) (O : MOrc Fk) : ∀ j, (mrun M n O j).length = j
  | 0 => rfl
  | j + 1 => by simp [mrun, mrun_length M n O j]

lemma mrun_take (M : QMM Fk) (n : ℕ) (O : MOrc Fk) : ∀ T j, j ≤ T → (mrun M n O T).take j = mrun M n O j
  | 0, j, h => by obtain rfl : j = 0 := by omega
                  rfl
  | T + 1, j, h => by
    rcases Nat.lt_or_ge j (T+1) with hj | hj
    · show (mrun M n O T ++ _).take j = _
      rw [List.take_append_of_le_length (by rw [mrun_length]; omega)]
      exact mrun_take M n O T j (by omega)
    · obtain rfl : j = T + 1 := by omega
      exact List.take_of_length_le (by rw [mrun_length])

variable (inp : ℕ → List (tm.Γ tm.k₀)) (acc : List (tm.Γ tm.k₁)) (T : ℕ → ℕ)

/-- Replay lemma: replaying the query machine's answers is the TM's run under Aenc E O. -/
lemma replay_mrun (n : ℕ) (O : MOrc Fk) : ∀ j,
    replay E tm (inp n) (mrun (simQ E tm inp acc T) n O j) =
      (flip bind (tm.step (Aenc E O)))^[j] (some (tm.initList (inp n)))
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', ← replay_mrun n O j]
    show replay E tm (inp n) (mrun (simQ E tm inp acc T) n O j ++ [_]) = _
    rw [replay_snoc]
    cases h : replay E tm (inp n) (mrun (simQ E tm inp acc T) n O j) with
    | none => rfl
    | some c =>
      show stepW tm _ c = tm.step (Aenc E O) c
      rw [step_eq]
      congr 1
      have hn : (simQ E tm inp acc T).next n (mrun (simQ E tm inp acc T) n O j) = qOf E (tm.query c) := by
        show (match replay E tm (inp n) _ with | some c => qOf E (tm.query c) | none => E.dummy) = _
        rw [h]
      rw [hn]
      simp [Aenc]

lemma out_iff (n : ℕ) (O : MOrc Fk) :
    (simQ E tm inp acc T).out n (mrun (simQ E tm inp acc T) n O (T n)) = true ↔
      Nonempty (OTM2OutputsInTime (Aenc E O) tm (inp n) (some acc) (T n)) := by
  show decide _ = true ↔ _
  rw [decide_eq_true_iff, mrun_length]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [mrun_take _ _ _ _ _ hj, replay_mrun] at h
    exact ⟨⟨⟨j, h⟩, hj⟩⟩
  · rintro ⟨⟨⟨j, h⟩, hj⟩⟩
    refine ⟨j, hj, ?_⟩
    rw [mrun_take _ _ _ _ _ hj, replay_mrun]; exact h

/-- AW Theorem 5.3 in the BGS Turing-machine model (steps 1-5): for every bit-encoding E of
field queries there are a Boolean oracle A (as a BGS oracle B), multiquadratic extensions P over
every field in the family, with sepLang B in NP^B but not in P^(Aenc E (mOrc P)). -/
theorem aw_tm_separation (E : Enc Fk) :
    ∃ (A : (m : ℕ) → (Fin m → Bool) → Bool) (P : ∀ k, (m : ℕ) → MvPolynomial (Fin m) (Fk k)) (B : Oracle),
      (∀ k m, (∀ j, degreeOf j (P k m) ≤ 2) ∧ ∀ z, eval (HHH.AW.bool z) (P k m) = if A m z then 1 else 0) ∧
      (∀ s, s ∈ B ↔ ∃ m z, A m z = true ∧ s = List.ofFn z ++ List.replicate m false) ∧
      InNP B (fin_encoding_string Bool) (sepLang B) ∧
      ¬ InP (Aenc E (mOrc P)) (fin_encoding_string Bool) (sepLang B) := by
  let Mi : ℕ → QMM Fk := fun i => simQ E (dEnum i).N.toOracleFinTM2 (dEnum i).input
    [(dEnum i).outE.symm true] (fun n => (dEnum i).time.eval n)
  have hT : ∀ i, ∃ N, ∀ n, N ≤ n → (Mi i).time n < 2 ^ n := fun i => eventually_eval_lt_two_pow _
  choose N hN using hT
  obtain ⟨nA, A, P, hext, hspread, hsupp, hwin⟩ := theorem_5_3_spread Mi N hN
  let B : Oracle := {s | ∃ m z, A m z = true ∧ s = List.ofFn z ++ List.replicate m false}
  refine ⟨A, P, B, hext, fun s => Iff.rfl, sepLang_inNP B, ?_⟩
  have hL : ∀ i, sepLang B (List.replicate (nA i) false) ↔ ∃ z, A (nA i) z = true := by
    intro i
    rw [sepLang_replicate_iff]
    constructor
    · rintro ⟨u, hu, m, z, hz, he⟩
      have hlen := congrArg List.length he
      simp only [List.length_append, List.length_replicate, List.length_ofFn] at hlen
      obtain ⟨j, rfl⟩ := hsupp m z hz
      have hji : j = i := by
        rcases lt_trichotomy j i with h | h | h
        · have := hspread j i h; omega
        · exact h
        · have := hspread i j h; omega
      subst hji; exact ⟨z, hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨List.ofFn z, by simp, nA i, z, hz, rfl⟩
  rintro ⟨f, h, hf⟩
  obtain ⟨c, -, hc⟩ := exists_dcode_decides h
  obtain ⟨i, rfl⟩ := dEnum_surjective c
  have hB := hc (List.replicate (nA i) false)
  rw [List.length_replicate] at hB
  obtain ⟨hB⟩ := hB
  have hout := out_iff E (dEnum i).N.toOracleFinTM2 (dEnum i).input [(dEnum i).outE.symm true]
    (fun n => (dEnum i).time.eval n) (nA i) (mOrc P)
  have hw := hwin i
  by_cases hz : ∃ z, A (nA i) z = true
  · have hf1 : f (List.replicate (nA i) false) = true := (hf _).mp ((hL i).mpr hz)
    rw [hf1] at hB
    exact (hw.mp (hout.mpr ⟨hB⟩)) hz
  · have h1 := hout.mp (hw.mpr hz)
    have h1' : Nonempty (OTM2OutputsInTime (Aenc E (mOrc P)) (dEnum i).N.toOracleFinTM2
        ((List.replicate (nA i) false).map (dEnum i).inE.symm) (some [(dEnum i).outE.symm true])
        ((dEnum i).time.eval (nA i))) := h1
    have e := (OTM2OutputsInTime.bool_iff (tm := (dEnum i).N.toOracleFinTM2) (dEnum i).outE hB true).mp h1'
    exact hz ((hL i).mp ((hf _).mpr e.symm))

end HHH.Bridge
