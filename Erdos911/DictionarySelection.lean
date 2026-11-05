import Erdos911.DictionaryGoodRows

open MeasureTheory

namespace Erdos911

/-- One binary-word dictionary is good on most of any prescribed
nonnegative block mass. Test families may differ between blocks. -/
theorem exists_dictionary_good_mass {L C R I : Type*}
    [Fintype L] [DecidableEq L] [Fintype C] [DecidableEq C]
    [DecidableEq R] [Fintype I]
    (T : I → Type*) [∀ i, Fintype (T i)]
    (N : ∀ i, T i → R → Finset L) (U : ∀ i, T i → Finset R)
    (s J maxTests : ℕ) (ε : ℝ)
    (hmin : ∀ i t y, y ∈ U i t → s ≤ (N i t y).card)
    (hcount : ∀ i, Fintype.card (T i) ≤ maxTests)
    (hbudget : (maxTests : ℝ) * (8 * (Fintype.card C : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) ^ J ≤ ε)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ ω : (L × C) → Bool,
      (1 - ε) * (∑ i : I, w i) ≤
        ∑ i : I, if (∀ t : T i,
          (eventHitSet (dictionaryBadCoordinate (N i t) (U i t)) Finset.univ ω).card < J)
          then w i else 0 := by
  classical
  let μ := bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)
  let E := fun i (t : T i) => {ω : (L × C) → Bool |
    J ≤ (eventHitSet (dictionaryBadCoordinate (N i t) (U i t)) Finset.univ ω).card}
  let A := fun i => ⋃ t : T i, E i t
  let p : ℝ := (8 * (Fintype.card C : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) ^ J
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hprob (i : I) : μ.real (A i) ≤ ε := by
    have hsingle (t : T i) : μ.real (E i t) ≤ p :=
      dictionary_bad_coordinates_tail (N i t) (U i t) s J (hmin i t)
    have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (T i))) => hsingle t)
    have hsum' : (∑ t : T i, μ.real (E i t)) ≤ Fintype.card (T i) * p := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
    have hcount' : (Fintype.card (T i) : ℝ) ≤ maxTests := by exact_mod_cast hcount i
    exact ((measureReal_iUnion_fintype_le (E i)).trans hsum').trans
      ((mul_le_mul_of_nonneg_right hcount' hp).trans hbudget)
  obtain ⟨ω, _, hcost⟩ := exists_conditional_cost_le μ Set.univ (by simp)
    A w (fun _ => ε) hw (by intro i; simpa only [Set.inter_univ, probReal_univ, div_one] using hprob i)
  have hbad : (∑ i : I, if ω ∈ A i then w i else 0) ≤ ε * (∑ i : I, w i) := by
    simpa only [Set.indicator, ← Finset.mul_sum] using hcost
  have hpartition : (∑ i : I, if ω ∉ A i then w i else 0) +
      (∑ i : I, if ω ∈ A i then w i else 0) = ∑ i : I, w i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ω ∈ A i <;> simp [hi]
  have hgood : (1 - ε) * (∑ i : I, w i) ≤ ∑ i : I, if ω ∉ A i then w i else 0 := by
    nlinarith only [hbad, hpartition]
  refine ⟨ω, ?_⟩
  convert hgood using 1
  apply Finset.sum_congr rfl
  intro i _
  have heq : (ω ∉ A i) ↔ ∀ t : T i,
      (eventHitSet (dictionaryBadCoordinate (N i t) (U i t)) Finset.univ ω).card < J := by
    simp only [A, E, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le]
  simp only [heq]

end Erdos911
