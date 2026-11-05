import Erdos911.BiasedBits
import Erdos911.BinomialEntropy
import Mathlib.Data.Finset.Powerset

open MeasureTheory

namespace Erdos911

noncomputable def markedElements {E : Type*} (S : Finset E) (ω : E → Bool) : Finset E := by
  classical
  exact S.filter (fun e => ω e = true)

/-- At least t successes contain an entirely marked t-subset. This gives
the elementary binomial union bound without assuming a rate approximation. -/
theorem marked_elements_tail {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (t : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitProductMeasure E p hp0 hp1).real {ω | t ≤ (markedElements S ω).card} ≤
      (S.card.choose t : ℝ) * p ^ t := by
  classical
  let A (T : ↥(S.powersetCard t)) := fixedBits T.val true
  have hcover : {ω | t ≤ (markedElements S ω).card} ⊆ ⋃ T, A T := by
    intro ω hω
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
    have hTS : T ⊆ S := hT.trans (Finset.filter_subset (fun e => ω e = true) S)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨T, Finset.mem_powersetCard.mpr ⟨hTS, hcard⟩⟩, ?_⟩
    intro e he
    exact (Finset.mem_filter.mp (hT he)).2
  have hsum : (∑ T : ↥(S.powersetCard t), (bitProductMeasure E p hp0 hp1).real (A T)) =
      (S.card.choose t : ℝ) * p ^ t := by
    have hpoint (T : ↥(S.powersetCard t)) : (bitProductMeasure E p hp0 hp1).real (A T) = p ^ t := by
      rw [bitProductMeasure_fixedBits]
      simp only [bernoulliWeight, ite_true, (Finset.mem_powersetCard.mp T.property).2]
    simp only [hpoint, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      Finset.card_powersetCard, nsmul_eq_mul]
  exact ((measureReal_mono hcover).trans (measureReal_iUnion_fintype_le A)).trans_eq hsum

theorem choose_mul_pow_bound (N t : ℕ) (ht : 0 < t) (hNt : t ≤ N)
    (p : ℝ) (hp : 0 ≤ p) :
    (N.choose t : ℝ) * p ^ t ≤ (Real.exp 1 * N * p / t) ^ t := by
  have hN : (0 : ℝ) < N := by exact_mod_cast ht.trans_le hNt
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have heq : Real.exp ((t : ℝ) * (Real.log ((N : ℝ) / t) + 1)) =
      (Real.exp 1 * N / t) ^ t := by
    rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log (div_pos hN htR)]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_right (choose_exp_upper_bound N t) (pow_nonneg hp t)
  rw [heq, ← mul_pow] at h
  convert h using 1
  congr 1
  ring

theorem marked_elements_tail_ratio {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (t a : ℕ) (ht : 0 < t) (hSa : S.card ≤ a * t)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitProductMeasure E p hp0 hp1).real {ω | t ≤ (markedElements S ω).card} ≤
      ((a : ℝ) * Real.exp 1 * p) ^ t := by
  by_cases htS : t ≤ S.card
  · have hbase : Real.exp 1 * S.card * p / t ≤ (a : ℝ) * Real.exp 1 * p := by
      apply (div_le_iff₀ (by exact_mod_cast ht : (0 : ℝ) < t)).mpr
      have hnat : (S.card : ℝ) ≤ (a : ℝ) * t := by exact_mod_cast hSa
      have h := mul_le_mul_of_nonneg_left hnat (mul_nonneg (Real.exp_pos 1).le hp0)
      nlinarith only [h]
    exact ((marked_elements_tail S t p hp0 hp1).trans (choose_mul_pow_bound S.card t ht htS p hp0)).trans
      (pow_le_pow_left₀ (by positivity) hbase t)
  · have hempty : {ω : E → Bool | t ≤ (markedElements S ω).card} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact htS (hω.trans (Finset.card_le_card (Finset.filter_subset (fun e => ω e = true) S)))
    rw [hempty, measureReal_empty]
    positivity

end Erdos911
