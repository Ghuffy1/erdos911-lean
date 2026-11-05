import Erdos911.ProductCoordinates

open MeasureTheory

namespace Erdos911

/-- A union bound inside a positive-probability conditioning event gives
an outcome avoiding all remaining forbidden events. -/
theorem exists_avoiding_inside_event {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Good : Set Ω) (hGood : 0 < μ.real Good)
    (B : I → Set Ω) (b : ℝ)
    (hB : ∀ i, μ.real (B i ∩ Good) / μ.real Good ≤ b)
    (hbudget : (Fintype.card I : ℝ) * b < 1) :
    ∃ ω ∈ Good, ∀ i, ω ∉ B i := by
  classical
  by_contra h
  push Not at h
  have hsub : Good ⊆ ⋃ i, B i ∩ Good := by
    intro ω hω
    obtain ⟨i, hi⟩ := h ω hω
    exact Set.mem_iUnion.mpr ⟨i, hi, hω⟩
  have htotal : μ.real Good ≤ ∑ i, μ.real (B i ∩ Good) :=
    (measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)
  have hlower : 1 ≤ (∑ i, μ.real (B i ∩ Good)) / μ.real Good :=
    (one_le_div hGood).mpr htotal
  have hupper : (∑ i, μ.real (B i ∩ Good)) / μ.real Good ≤ (Fintype.card I : ℝ) * b := by
    rw [Finset.sum_div]
    have hsum : (∑ i : I, μ.real (B i ∩ Good) / μ.real Good) ≤ ∑ _i : I, b :=
      Finset.sum_le_sum (fun i _ => hB i)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    exact hsum
  exact (not_le_of_gt hbudget) (hlower.trans hupper)

end Erdos911
