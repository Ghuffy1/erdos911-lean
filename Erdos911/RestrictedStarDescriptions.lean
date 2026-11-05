import Erdos911.RestrictedStarCounting

namespace Erdos911

/-- The union over bounded assigned-edge counts with a required total
logarithmic deficit, for fixed witness neighborhoods. -/
noncomputable def restrictedStarDescriptions {I E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] (U : Finset E) (A : I → Finset E) (C : I → ℕ)
    (a D P : ℕ) (W : ℝ) : Finset (Finset E) := by
  classical
  exact (Fintype.piFinset (fun _ : I => Finset.range (D + 1))).biUnion (fun t =>
    if (∑ i, t i) ≤ a ∧ W ≤ ∑ i, (t i : ℝ) * Real.log ((P : ℝ) / C i) then
      restrictedStarSubsets U A (a - ∑ i, t i) t else ∅)

theorem mem_restrictedStarDescriptions {I E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] (U : Finset E) (A : I → Finset E) (C : I → ℕ)
    (a D P : ℕ) (W : ℝ) (F : Finset E) :
    F ∈ restrictedStarDescriptions U A C a D P W ↔
      ∃ t : I → ℕ, (∀ i, t i ≤ D) ∧ (∑ i, t i) ≤ a ∧
        W ≤ ∑ i, (t i : ℝ) * Real.log ((P : ℝ) / C i) ∧
        F ∈ restrictedStarSubsets U A (a - ∑ i, t i) t := by
  classical
  simp only [restrictedStarDescriptions, Finset.mem_biUnion, Fintype.mem_piFinset,
    Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨t, ht, hF⟩
    split_ifs at hF with hadmissible
    · exact ⟨t, ht, hadmissible.1, hadmissible.2, hF⟩
    · exact (Finset.notMem_empty _ hF).elim
  · rintro ⟨t, ht, hsize, hdeficit, hF⟩
    exact ⟨t, ht, by simpa only [ite_eq_left (And.intro hsize hdeficit)] using hF⟩

theorem restrictedStarDescriptions_card_bound {I E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] (U : Finset E) (A : I → Finset E) (C : I → ℕ)
    (a D P : ℕ) (W : ℝ) (hP : 0 < P) (hC : ∀ i, 0 < C i)
    (hk : 0 < Fintype.card I) (ha : 0 < a)
    (hU : U.card ≤ P * Fintype.card I) (hA : ∀ i, (A i).card ≤ C i) :
    ((restrictedStarDescriptions U A C a D P W).card : ℝ) ≤
      ((D + 1 : ℕ) : ℝ) ^ Fintype.card I *
        Real.exp ((a : ℝ) * Real.log ((P * Fintype.card I : ℝ) / a) - W + 2 * a) := by
  classical
  let T := Fintype.piFinset (fun _ : I => Finset.range (D + 1))
  let patterns := fun t : I → ℕ =>
    if (∑ i, t i) ≤ a ∧ W ≤ ∑ i, (t i : ℝ) * Real.log ((P : ℝ) / C i) then
      restrictedStarSubsets U A (a - ∑ i, t i) t else ∅
  let bound := Real.exp ((a : ℝ) * Real.log ((P * Fintype.card I : ℝ) / a) - W + 2 * a)
  have hbound : ∀ t : I → ℕ, ((patterns t).card : ℝ) ≤ bound := by
    intro t
    dsimp only [patterns]
    split_ifs with hadmissible
    · have h := restrictedStarSubsets_exp_bound U A a (a - ∑ i, t i) P C t
        hP hC hk ha hU hA (Nat.sub_add_cancel hadmissible.1).symm
      apply h.trans
      apply Real.exp_le_exp.mpr
      linarith only [hadmissible.2]
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact (Real.exp_pos _).le
  have hcount : (restrictedStarDescriptions U A C a D P W).card ≤
      ∑ t ∈ T, (patterns t).card := Finset.card_biUnion_le
  have hT : T.card = (D + 1) ^ Fintype.card I := by
    dsimp only [T]
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ]
  calc
    ((restrictedStarDescriptions U A C a D P W).card : ℝ) ≤
        ∑ t ∈ T, ((patterns t).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _t ∈ T, bound := Finset.sum_le_sum (fun t _ => hbound t)
    _ = ((D + 1 : ℕ) : ℝ) ^ Fintype.card I * bound := by
      rw [Finset.sum_const, nsmul_eq_mul, hT, Nat.cast_pow]

theorem witness_restrictedStarDescriptions_card_bound {I E Q : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq E] [DecidableEq Q]
    (witnesses : Finset Q) (U : Finset E) (A : Q → I → Finset E) (C : Q → I → ℕ)
    (a D P : ℕ) (W : ℝ) (hP : 0 < P)
    (hC : ∀ q ∈ witnesses, ∀ i, 0 < C q i) (hk : 0 < Fintype.card I) (ha : 0 < a)
    (hU : U.card ≤ P * Fintype.card I) (hA : ∀ q ∈ witnesses, ∀ i, (A q i).card ≤ C q i) :
    ((witnesses.biUnion (fun q => restrictedStarDescriptions U (A q) (C q) a D P W)).card : ℝ) ≤
      witnesses.card * ((D + 1 : ℕ) : ℝ) ^ Fintype.card I *
        Real.exp ((a : ℝ) * Real.log ((P * Fintype.card I : ℝ) / a) - W + 2 * a) := by
  let bound := ((D + 1 : ℕ) : ℝ) ^ Fintype.card I *
    Real.exp ((a : ℝ) * Real.log ((P * Fintype.card I : ℝ) / a) - W + 2 * a)
  have hcard := Finset.card_biUnion_le (s := witnesses)
    (t := fun q => restrictedStarDescriptions U (A q) (C q) a D P W)
  calc
    ((witnesses.biUnion (fun q => restrictedStarDescriptions U (A q) (C q) a D P W)).card : ℝ) ≤
        ∑ q ∈ witnesses, ((restrictedStarDescriptions U (A q) (C q) a D P W).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _q ∈ witnesses, bound := Finset.sum_le_sum (fun q hq =>
      restrictedStarDescriptions_card_bound U (A q) (C q) a D P W hP (hC q hq) hk ha hU (hA q hq))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; dsimp only [bound]; ring

end Erdos911
