import Erdos911.DyadicBudget

namespace Erdos911

theorem dyadic_linear_sum_identity (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ) * (1 / 2 : ℝ) ^ j) +
      (2 * (n : ℝ) + 2) * (1 / 2 : ℝ) ^ n = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    push_cast
    nlinarith only [ih]

theorem dyadic_linear_sum_le (n : ℕ) :
    (∑ j ∈ Finset.range n, (j : ℝ) * (1 / 2 : ℝ) ^ j) ≤ 2 := by
  have h := dyadic_linear_sum_identity n
  have hp : 0 ≤ (2 * (n : ℝ) + 2) * (1 / 2 : ℝ) ^ n := by positivity
  linarith only [h, hp]

theorem dyadic_affine_sum_le (n : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∑ j : Fin n, (1 / 2 : ℝ) ^ j.val * (a + b * j.val)) ≤ 2 * (a + b) := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1 / 2 : ℝ) ^ j * (a + b * j)) n]
  have hs : (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j * (a + b * j)) =
      a * (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j) +
        b * (∑ j ∈ Finset.range n, (j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  have h₁ := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) ha
  have h₂ := mul_le_mul_of_nonneg_left (dyadic_linear_sum_le n) hb
  nlinarith only [h₁, h₂]

theorem reverse_dyadic_power (n j : ℕ) (hj : j ≤ n) :
    (2 : ℝ) ^ (n - j) = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ j := by
  rw [div_pow, one_pow, mul_one_div, eq_div_iff (by positivity : (2 : ℝ) ^ j ≠ 0)]
  rw [← pow_add, Nat.sub_add_cancel hj]

end Erdos911
