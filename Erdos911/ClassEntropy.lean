import Erdos911.EntropyPartition

namespace Erdos911

noncomputable def dimensionCodeCost (L : ℝ) (p : ℕ × ℕ) : ℝ :=
  L * p.2 + ((p.1 + p.2 : ℕ) : ℝ) * Real.log 2

theorem exp_neg_dimensionCodeCost (L : ℝ) (p : ℕ × ℕ) :
    Real.exp (-dimensionCodeCost L p) =
      Real.exp (-(L * p.2)) * (1 / 2 : ℝ) ^ (p.1 + p.2) := by
  unfold dimensionCodeCost
  have hhalf : Real.exp (-Real.log (2 : ℝ)) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [show -(L * p.2 + ((p.1 + p.2 : ℕ) : ℝ) * Real.log 2) =
    -(L * p.2) + ((p.1 + p.2 : ℕ) : ℝ) * (-Real.log 2) by ring,
    Real.exp_add, Real.exp_nat_mul, hhalf]

/-- The dimension code has total reference mass at most one whenever each
fixed order-and-size class satisfies its exponential cardinality bound. -/
theorem class_code_partition_le_one {I : Type*} [Fintype I]
    (label : I → ℕ × ℕ) (L : ℝ)
    (hpositive : ∀ i, 0 < (label i).1 ∧ 0 < (label i).2)
    (hclass : ∀ p, (((Finset.univ : Finset I).filter (fun i => label i = p)).card : ℝ) ≤
      Real.exp (L * p.2)) :
    (∑ i, Real.exp (-dimensionCodeCost L (label i))) ≤ 1 := by
  classical
  let P := (Finset.univ : Finset I).image label
  let weight := fun p : ℕ × ℕ => Real.exp (-(L * p.2)) * (1 / 2 : ℝ) ^ (p.1 + p.2)
  have hsum : (∑ i, Real.exp (-dimensionCodeCost L (label i))) =
      ∑ p ∈ P, (((Finset.univ : Finset I).filter (fun i => label i = p)).card : ℝ) * weight p := by
    simp_rw [exp_neg_dimensionCodeCost]
    symm
    calc
      (∑ p ∈ P, (((Finset.univ : Finset I).filter (fun i => label i = p)).card : ℝ) * weight p) =
          ∑ p ∈ P, ∑ _i ∈ (Finset.univ : Finset I).filter (fun i => label i = p), weight p := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ i, weight (label i) := Finset.sum_fiberwise_of_maps_to'
        (fun i (_ : i ∈ (Finset.univ : Finset I)) => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) weight
  have hpoint (p : ℕ × ℕ) :
      (((Finset.univ : Finset I).filter (fun i => label i = p)).card : ℝ) * weight p ≤
        (1 / 2 : ℝ) ^ (p.1 + p.2) := by
    calc
      (((Finset.univ : Finset I).filter (fun i => label i = p)).card : ℝ) * weight p ≤
          Real.exp (L * p.2) * weight p := mul_le_mul_of_nonneg_right (hclass p) (by positivity)
      _ = (1 / 2 : ℝ) ^ (p.1 + p.2) := by
        dsimp only [weight]
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [hsum]
  exact (Finset.sum_le_sum (fun p _ => hpoint p)).trans
    (positive_pair_geometric_sum_le_one P (by
      intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact hpositive i))

theorem weighted_class_entropy_bound {I : Type*} [Fintype I]
    (t : I → ℕ) (label : I → ℕ × ℕ) (L : ℝ)
    (hr : 0 < ∑ i, (t i : ℝ))
    (hpositive : ∀ i, 0 < (label i).1 ∧ 0 < (label i).2)
    (hclass : ∀ p, (((Finset.univ : Finset I).filter (fun i => label i = p)).card : ℝ) ≤
      Real.exp (L * p.2)) :
    multiplicityEntropy t ≤ L * (∑ i, (t i : ℝ) * (label i).2) +
      Real.log 2 * ((∑ i, (t i : ℝ) * (label i).1) + ∑ i, (t i : ℝ) * (label i).2) := by
  have h := multiplicityEntropy_le_cost t (fun i => dimensionCodeCost L (label i)) hr
    (class_code_partition_le_one label L hpositive hclass)
  calc
    multiplicityEntropy t ≤ ∑ i, (t i : ℝ) * dimensionCodeCost L (label i) := h
    _ = ∑ i, (L * ((t i : ℝ) * (label i).2) + Real.log 2 * ((t i : ℝ) * (label i).1) +
        Real.log 2 * ((t i : ℝ) * (label i).2)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold dimensionCodeCost
      push_cast
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

end Erdos911
