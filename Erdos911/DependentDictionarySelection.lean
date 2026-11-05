import Erdos911.ConcreteDictionarySelection

open MeasureTheory

namespace Erdos911

/-- The weighted dictionary selection also permits different right
vertex types for different target blocks. -/
theorem exists_dependent_dictionary {I : Type*} [Fintype I]
    (q : ℕ) (hq : 65536 ≤ q) (R T : I → Type*)
    [∀ i, DecidableEq (R i)] [∀ i, Fintype (T i)]
    (N : ∀ i, T i → R i → Finset (Fin (dictionaryLabelCount q)))
    (U : ∀ i, T i → Finset (R i))
    (hmin : ∀ i t y, y ∈ U i t → dictionaryRowMinimum q ≤ (N i t y).card)
    (hcount : ∀ i, Fintype.card (T i) ≤ dictionaryTestCount q)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool,
      (7 / 8 : ℝ) * (∑ i : I, w i) ≤
        ∑ i : I, if (∀ t : T i,
          (eventHitSet (dictionaryBadCoordinate (N i t) (U i t)) Finset.univ ω).card < dictionaryBadLimit q)
          then w i else 0 := by
  classical
  let L := Fin (dictionaryLabelCount q)
  let C := Fin (dictionaryWordLength q)
  let μ := bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)
  let E := fun i (t : T i) => {ω : (L × C) → Bool |
    dictionaryBadLimit q ≤ (eventHitSet (dictionaryBadCoordinate (N i t) (U i t)) Finset.univ ω).card}
  let A := fun i => ⋃ t : T i, E i t
  let p : ℝ := (8 * (dictionaryWordLength q : ℝ) ^ 2 * (1 / 2 : ℝ) ^ dictionaryRowMinimum q) ^ dictionaryBadLimit q
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hprob (i : I) : μ.real (A i) ≤ 1 / 8 := by
    have ht (t : T i) : μ.real (E i t) ≤ p := by
      simpa only [C, Fintype.card_fin] using
        dictionary_bad_coordinates_tail (L := L) (C := C) (R := R i)
          (N i t) (U i t) (dictionaryRowMinimum q) (dictionaryBadLimit q) (hmin i t)
    have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (T i))) => ht t)
    have hs : (∑ t : T i, μ.real (E i t)) ≤ Fintype.card (T i) * p := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
    have hc : (Fintype.card (T i) : ℝ) ≤ dictionaryTestCount q := by exact_mod_cast hcount i
    exact ((measureReal_iUnion_fintype_le (E i)).trans hs).trans
      ((mul_le_mul_of_nonneg_right hc hp).trans (dictionary_failure_budget q hq))
  obtain ⟨ω, _, hcost⟩ := exists_conditional_cost_le μ Set.univ (by simp)
    A w (fun _ => 1 / 8) hw (by intro i; simpa only [Set.inter_univ, probReal_univ, div_one] using hprob i)
  have hbad : (∑ i : I, if ω ∈ A i then w i else 0) ≤ (1 / 8 : ℝ) * (∑ i : I, w i) := by
    simpa only [Set.indicator, ← Finset.mul_sum] using hcost
  have hpartition : (∑ i : I, if ω ∉ A i then w i else 0) +
      (∑ i : I, if ω ∈ A i then w i else 0) = ∑ i : I, w i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ω ∈ A i <;> simp [hi]
  have hg : (7 / 8 : ℝ) * (∑ i : I, w i) ≤ ∑ i : I, if ω ∉ A i then w i else 0 := by
    linarith only [hbad, hpartition]
  refine ⟨ω, ?_⟩
  convert hg using 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : (ω ∉ A i) ↔ ∀ t : T i,
      (eventHitSet (dictionaryBadCoordinate (N i t) (U i t)) Finset.univ ω).card < dictionaryBadLimit q := by
    simp only [A, E, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le]
  simp only [heq]

end Erdos911
