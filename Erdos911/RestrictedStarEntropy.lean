import Erdos911.EntropyPartition
import Erdos911.BinomialEntropy

namespace Erdos911

theorem multiplicityEntropy_le_log_card {I : Type*} [Fintype I]
    (t : I → ℕ) (hk : 0 < Fintype.card I) :
    multiplicityEntropy t ≤ (∑ i, (t i : ℝ)) * Real.log (Fintype.card I) := by
  by_cases hzero : (∑ i, t i) = 0
  · have htzero : ∀ i, t i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    simp [multiplicityEntropy, htzero]
  have hr : 0 < ∑ i, (t i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hkreal : (0 : ℝ) < Fintype.card I := by exact_mod_cast hk
  have hpartition : (∑ _i : I, Real.exp (-Real.log (Fintype.card I : ℝ))) ≤ 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Real.exp_neg, Real.exp_log hkreal]
    exact le_of_eq (mul_inv_cancel₀ hkreal.ne')
  have h := multiplicityEntropy_le_cost t (fun _ => Real.log (Fintype.card I)) hr hpartition
  simpa only [← Finset.sum_mul] using h

/-- Restricting the available neighborhood at each role saves the sum of
the logarithmic deficits, even when some roles are assigned no edges. -/
theorem restricted_star_log_sum_bound {I : Type*} [Fintype I]
    (P : ℝ) (C : I → ℝ) (t : I → ℕ) (hP : 0 < P)
    (hC : ∀ i, 0 < C i) (hk : 0 < Fintype.card I) :
    (∑ i, (t i : ℝ) * Real.log (C i / t i)) +
      (∑ i, (t i : ℝ) * Real.log (P / C i)) ≤
        (∑ i, (t i : ℝ)) *
          Real.log (P * Fintype.card I / (∑ i, (t i : ℝ))) := by
  have hkreal : (0 : ℝ) < Fintype.card I := by exact_mod_cast hk
  have hfirst : (∑ i, (t i : ℝ) * Real.log (C i / t i)) =
      (∑ i, (t i : ℝ) * Real.log (C i)) - ∑ i, (t i : ℝ) * Real.log (t i : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => weighted_log_div_eq (C i) (t i) (hC i))
  have hdeficit : (∑ i, (t i : ℝ) * Real.log (P / C i)) =
      (∑ i, (t i : ℝ)) * Real.log P - ∑ i, (t i : ℝ) * Real.log (C i) := by
    simp_rw [Real.log_div hP.ne' (hC _).ne', mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  have h := multiplicityEntropy_le_log_card t hk
  unfold multiplicityEntropy at h
  rw [hfirst, hdeficit, weighted_log_div_eq (P * Fintype.card I) _ (mul_pos hP hkreal),
    Real.log_mul hP.ne' hkreal.ne']
  nlinarith only [h]

theorem two_part_entropy_merge (M a b t : ℝ) (hM : 0 < M) (ha : 0 < a)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hsplit : a = b + t) :
    b * Real.log (M / b) + t * Real.log (M / t) ≤ a * Real.log (M / a) + a := by
  have hleft := weighted_log_div_le a b ha hb
  have hright := weighted_log_div_le a t ha ht
  rw [weighted_log_div_eq a b ha] at hleft
  rw [weighted_log_div_eq a t ha] at hright
  rw [weighted_log_div_eq M b hM, weighted_log_div_eq M t hM,
    weighted_log_div_eq M a hM]
  rw [hsplit] at hleft hright ⊢
  nlinarith only [hleft, hright]

theorem restricted_star_entropy_bound {I : Type*} [Fintype I]
    (P : ℝ) (C : I → ℝ) (t : I → ℕ) (a b : ℝ)
    (hP : 0 < P) (hC : ∀ i, 0 < C i) (hk : 0 < Fintype.card I)
    (ha : 0 < a) (hb : 0 ≤ b) (hsplit : a = b + ∑ i, (t i : ℝ)) :
    b * (Real.log (P * Fintype.card I / b) + 1) +
      (∑ i, (t i : ℝ) * (Real.log (C i / t i) + 1)) ≤
        a * Real.log (P * Fintype.card I / a) -
          (∑ i, (t i : ℝ) * Real.log (P / C i)) + 2 * a := by
  have hkreal : (0 : ℝ) < Fintype.card I := by exact_mod_cast hk
  have hstar := restricted_star_log_sum_bound P C t hP hC hk
  have hmerge := two_part_entropy_merge (P * Fintype.card I) a b (∑ i, (t i : ℝ))
    (mul_pos hP hkreal) ha hb (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) hsplit
  simp only [mul_add, mul_one, Finset.sum_add_distrib] at *
  linarith

/-- The binomial enumeration for a fixed restricted-star assignment has
a uniform linear entropy error and its full weighted deficit saving. -/
theorem restricted_star_choose_product_bound {I : Type*} [Fintype I]
    (P a b : ℕ) (C t : I → ℕ) (hP : 0 < P) (hC : ∀ i, 0 < C i)
    (hk : 0 < Fintype.card I) (ha : 0 < a) (hsplit : a = b + ∑ i, t i) :
    (((P * Fintype.card I).choose b : ℝ) * ∏ i, ((C i).choose (t i) : ℝ)) ≤
      Real.exp ((a : ℝ) * Real.log ((P * Fintype.card I : ℝ) / a) -
        (∑ i, (t i : ℝ) * Real.log ((P : ℝ) / C i)) + 2 * a) := by
  have hscalar := restricted_star_entropy_bound (I := I) P (fun i => (C i : ℝ)) t a b
    (by exact_mod_cast hP) (fun i => by exact_mod_cast hC i) hk
    (by exact_mod_cast ha) (Nat.cast_nonneg _) (by exact_mod_cast hsplit)
  have hprod : (∏ i, ((C i).choose (t i) : ℝ)) ≤
      ∏ i, Real.exp ((t i : ℝ) * (Real.log ((C i : ℝ) / t i) + 1)) := by
    exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      (fun i _ => choose_exp_upper_bound (C i) (t i))
  calc
    (((P * Fintype.card I).choose b : ℝ) * ∏ i, ((C i).choose (t i) : ℝ)) ≤
        Real.exp ((b : ℝ) * (Real.log (((P * Fintype.card I : ℕ) : ℝ) / b) + 1)) *
          ∏ i, Real.exp ((t i : ℝ) * (Real.log ((C i : ℝ) / t i) + 1)) :=
      mul_le_mul (choose_exp_upper_bound (P * Fintype.card I) b) hprod (by positivity) (by positivity)
    _ = Real.exp ((b : ℝ) * (Real.log ((P * Fintype.card I : ℝ) / b) + 1) +
        ∑ i, (t i : ℝ) * (Real.log ((C i : ℝ) / t i) + 1)) := by
      rw [← Real.exp_sum, ← Real.exp_add, Nat.cast_mul]
    _ ≤ _ := Real.exp_le_exp.mpr hscalar

end Erdos911
