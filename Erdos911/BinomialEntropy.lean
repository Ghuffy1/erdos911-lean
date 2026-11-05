import Erdos911.ForestEntropy
import Erdos911.RepeatedBlockCounting
import Mathlib.Data.Nat.Choose.Bounds

namespace Erdos911

theorem weighted_log_div_eq (A x : ℝ) (hA : 0 < A) :
    x * Real.log (A / x) = x * Real.log A - x * Real.log x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hA.ne' hx]
    ring

theorem weighted_log_div_le (A x : ℝ) (hA : 0 < A) (hx : 0 ≤ x) :
    x * Real.log (A / x) ≤ A - x := by
  by_cases hxzero : x = 0
  · simpa only [hxzero, zero_mul, sub_zero] using hA.le
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  calc
    x * Real.log (A / x) ≤ x * (A / x - 1) :=
      mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hA hxpos)) hx
    _ = A - x := by field_simp

theorem log_choose_upper_bound (n k : ℕ) (hkn : k ≤ n) :
    Real.log (n.choose k : ℝ) ≤ (k : ℝ) * (Real.log ((n : ℝ) / k) + 1) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hkpos.trans_le hkn
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hcpos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hbound := Nat.choose_le_pow_div (α := ℝ) k n
  have hlog := Real.log_le_log hcpos hbound
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at hlog
  have hfac := log_factorial_lower_bound k
  rw [Real.log_div hnpos.ne' hkreal.ne']
  nlinarith

theorem choose_exp_upper_bound (n k : ℕ) :
    (n.choose k : ℝ) ≤ Real.exp ((k : ℝ) * (Real.log ((n : ℝ) / k) + 1)) := by
  by_cases hkn : k ≤ n
  · have hcpos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
    exact (Real.log_le_iff_le_exp hcpos).mp (log_choose_upper_bound n k hkn)
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkn), Nat.cast_zero]
    exact (Real.exp_pos _).le

/-- The entropy cost of designating disjoint pairs has a uniform linear
error, including vanishing pair or remainder counts. -/
theorem pair_entropy_merge (M R a j b : ℝ) (hM : 0 < M) (hR : 0 < R)
    (ha : 0 < a) (hj : 0 ≤ j) (hb : 0 ≤ b) (hab : a = 2 * j + b) :
    j * (Real.log (M * R / j) + 1) + b * (Real.log (M / b) + 1) ≤
      a * Real.log (M / a) - j * Real.log (M / (a * R)) + 2 * a := by
  have hleft := weighted_log_div_le a j ha hj
  have hright := weighted_log_div_le a b ha hb
  rw [weighted_log_div_eq a j ha] at hleft
  rw [weighted_log_div_eq a b ha] at hright
  rw [mul_add, mul_add, weighted_log_div_eq (M * R) j (mul_pos hM hR),
    weighted_log_div_eq M b hM, weighted_log_div_eq M a hM,
    Real.log_mul hM.ne' hR.ne',
    Real.log_div hM.ne' (mul_ne_zero ha.ne' hR.ne'), Real.log_mul ha.ne' hR.ne']
  rw [hab] at hleft hright ⊢
  nlinarith

theorem pair_choose_product_exp_bound (M R a j : ℕ)
    (hM : 0 < M) (hR : 0 < R) (hja : 2 * j ≤ a) :
    ((M * R).choose j : ℝ) * (M.choose (a - 2 * j) : ℝ) ≤
      Real.exp ((a : ℝ) * Real.log ((M : ℝ) / a) -
        (j : ℝ) * Real.log ((M : ℝ) / ((a : ℝ) * R)) + 2 * a) := by
  by_cases ha : a = 0
  · have hj : j = 0 := by omega
    simp [ha, hj]
  have ha_real : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hM_real : (0 : ℝ) < M := by exact_mod_cast hM
  have hR_real : (0 : ℝ) < R := by exact_mod_cast hR
  have hab : (a : ℝ) = 2 * j + (a - 2 * j : ℕ) := by
    norm_cast
    omega
  calc
    ((M * R).choose j : ℝ) * (M.choose (a - 2 * j) : ℝ) ≤
        Real.exp ((j : ℝ) * (Real.log (((M * R : ℕ) : ℝ) / j) + 1)) *
          Real.exp (((a - 2 * j : ℕ) : ℝ) *
            (Real.log ((M : ℝ) / ((a - 2 * j : ℕ) : ℝ)) + 1)) :=
      mul_le_mul (choose_exp_upper_bound (M * R) j)
        (choose_exp_upper_bound M (a - 2 * j)) (by positivity) (by positivity)
    _ = Real.exp ((j : ℝ) * (Real.log ((M : ℝ) * R / j) + 1) +
        ((a - 2 * j : ℕ) : ℝ) *
          (Real.log ((M : ℝ) / ((a - 2 * j : ℕ) : ℝ)) + 1)) := by
      rw [← Real.exp_add, Nat.cast_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (pair_entropy_merge M R a j (a - 2 * j : ℕ)
      hM_real hR_real ha_real (by positivity) (by positivity) hab)

/-- The exponential repeated-block estimate with an explicit error `2*a`.
The following component-type count must still account for image supports. -/
theorem repeatedBlockSubsets_exp_bound_of_bounded {V : Type*} [DecidableEq V]
    {R : ℕ} {P : Finset (RectangleBlock V)} (hP : BoundedEdgeBlocks P R)
    (T : Finset (Sym2 V)) (a j : ℕ)
    (hT : 0 < T.card) (hR : 0 < R) (hja : 2 * j ≤ a) :
    ((repeatedBlockSubsets P T a j).card : ℝ) ≤
      Real.exp ((a : ℝ) * Real.log ((T.card : ℝ) / a) -
        (j : ℝ) * Real.log ((T.card : ℝ) / ((a : ℝ) * R)) + 2 * a) := by
  have hcount : ((repeatedBlockSubsets P T a j).card : ℝ) ≤
      ((T.card * R).choose j : ℝ) * (T.card.choose (a - 2 * j) : ℝ) := by
    exact_mod_cast repeatedBlockSubsets_card_le_of_bounded hP T a j
  exact hcount.trans (pair_choose_product_exp_bound T.card R a j hT hR hja)

theorem repeatedBlockSubsets_exp_bound {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (T : Finset (Sym2 V)) (a j : ℕ)
    (hT : 0 < T.card) (hq : 0 < q) (hja : 2 * j ≤ a) :
    ((repeatedBlockSubsets P T a j).card : ℝ) ≤
      Real.exp ((a : ℝ) * Real.log ((T.card : ℝ) / a) -
        (j : ℝ) * Real.log ((T.card : ℝ) / ((a : ℝ) * (q * q))) + 2 * a) := by
  simpa only [Nat.cast_mul] using repeatedBlockSubsets_exp_bound_of_bounded
    hP.boundedEdgeBlocks T a j hT (Nat.mul_pos hq hq) hja

end Erdos911
