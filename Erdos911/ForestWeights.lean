import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Erdos911

/-- Weighted AM-GM in the form used to bound the product of host degrees
at the branching vertices of a rooted forest. -/
theorem weighted_degree_product_bound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (s : ι → ℕ) (M : ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hS : 0 < ∑ i, s i) (hM : (∑ i, a i) ≤ M) :
    (∏ i, (a i) ^ s i) ≤
      (M / (∑ i, s i : ℕ)) ^ (∑ i, s i) * ∏ i, (s i : ℝ) ^ s i := by
  let S : ℕ := ∑ i, s i
  let P : ℝ := ∏ i, (a i / (s i : ℝ)) ^ s i
  have hSreal : (0 : ℝ) < S := by exact_mod_cast hS
  have hsreal : ∀ i, (0 : ℝ) ≤ s i := fun i => Nat.cast_nonneg _
  have hweights : (∑ i, (s i : ℝ)) = (S : ℝ) := by simp [S]
  have hnum : (∑ i, (s i : ℝ) * (a i / (s i : ℝ))) ≤ ∑ i, a i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hsi : s i = 0
    · simpa only [hsi, Nat.cast_zero, zero_mul] using ha i
    · have hsne : (s i : ℝ) ≠ 0 := by exact_mod_cast hsi
      have heq : (s i : ℝ) * (a i / (s i : ℝ)) = a i := by field_simp
      exact heq.le
  have hmean := Real.geom_mean_le_arith_mean Finset.univ
    (fun i => (s i : ℝ)) (fun i => a i / (s i : ℝ))
    (fun i _ => hsreal i) (by simpa only [hweights] using hSreal)
    (fun i _ => div_nonneg (ha i) (hsreal i))
  have hmean' : P ^ ((S : ℝ)⁻¹) ≤ M / S := by
    apply le_trans (b := (∑ i, (s i : ℝ) * (a i / (s i : ℝ))) / S)
    · simpa only [Real.rpow_natCast, hweights, P] using hmean
    · exact div_le_div_of_nonneg_right (hnum.trans hM) hSreal.le
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => pow_nonneg
    (div_nonneg (ha i) (hsreal i)) _)
  have hraised := Real.rpow_le_rpow (Real.rpow_nonneg hP ((S : ℝ)⁻¹)) hmean' hSreal.le
  have hidentity : (P ^ ((S : ℝ)⁻¹)) ^ (S : ℝ) = P := by
    rw [← Real.rpow_mul hP, inv_mul_cancel₀ hSreal.ne', Real.rpow_one]
  rw [hidentity, Real.rpow_natCast] at hraised
  have hfactor : 0 ≤ ∏ i, (s i : ℝ) ^ s i :=
    Finset.prod_nonneg (fun i _ => pow_nonneg (hsreal i) _)
  calc
    (∏ i, (a i) ^ s i) = ∏ i, (a i / (s i : ℝ)) ^ s i * (s i : ℝ) ^ s i := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hsi : s i = 0
      · simp only [hsi, pow_zero, one_mul]
      · have hsne : (s i : ℝ) ≠ 0 := by exact_mod_cast hsi
        rw [← mul_pow, div_mul_cancel₀ (a i) hsne]
    _ = P * ∏ i, (s i : ℝ) ^ s i := Finset.prod_mul_distrib
    _ ≤ (M / S) ^ S * ∏ i, (s i : ℝ) ^ s i :=
      mul_le_mul_of_nonneg_right hraised hfactor

theorem child_degree_product_le {ι : Type*} [Fintype ι] (s : ι → ℕ) (D : ℕ)
    (hD : ∀ i, s i ≤ D) :
    (∏ i, (s i : ℝ) ^ s i) ≤ (D : ℝ) ^ (∑ i, s i) := by
  calc
    (∏ i, (s i : ℝ) ^ s i) ≤ ∏ i, (D : ℝ) ^ s i := by
      apply Finset.prod_le_prod₀
      · intro i _
        positivity
      · intro i _
        exact pow_le_pow_left₀ (show (0 : ℝ) ≤ (s i : ℝ) from Nat.cast_nonneg _)
          (show (s i : ℝ) ≤ (D : ℝ) by exact_mod_cast hD i) (s i)
    _ = (D : ℝ) ^ (∑ i, s i) := Finset.prod_pow_eq_pow_sum Finset.univ s (D : ℝ)

end Erdos911
