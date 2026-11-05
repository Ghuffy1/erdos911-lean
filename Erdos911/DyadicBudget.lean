import Erdos911.WeightedEdgeAssignment
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos911

def dyadicFloor (n : ℕ) : ℕ := 2 ^ Nat.log 2 n

theorem dyadicFloor_bounds (n : ℕ) (hn : 0 < n) :
    dyadicFloor n ≤ n ∧ n < 2 * dyadicFloor n := by
  refine ⟨Nat.pow_log_le_self 2 hn.ne', ?_⟩
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
  simpa only [dyadicFloor, pow_succ, Nat.mul_comm] using h

theorem dyadic_prefix_sum (N : ℕ) : (∑ j ∈ Finset.range N, 2 ^ j) + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Summing all dyadic scales that can charge a vertex costs at most
twice its original degree, independent of the number of scales. -/
theorem dyadic_supported_sum (N w : ℕ) :
    (∑ j ∈ Finset.range N, if 2 ^ j ≤ w then 2 ^ j else 0) ≤ 2 * w := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases h : 2 ^ N ≤ w
    · rw [ite_eq_left h]
      have hsum : (∑ j ∈ Finset.range N, if 2 ^ j ≤ w then 2 ^ j else 0) ≤
          ∑ j ∈ Finset.range N, 2 ^ j := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs <;> omega
      have hp := dyadic_prefix_sum N
      omega
    · simpa only [ite_eq_right h, add_zero] using ih

theorem dyadic_support_budget {V : Type*} [Fintype V] [DecidableEq V]
    (N : ℕ) (S : Fin N → Finset V) (w : V → ℕ)
    (hS : ∀ j v, v ∈ S j → 2 ^ j.val ≤ w v) :
    (∑ j : Fin N, ((S j).card : ℝ) * (2 : ℝ) ^ j.val) ≤ 2 * ∑ v, (w v : ℝ) := by
  rw [weighted_incidence_sum S (fun j => (2 : ℝ) ^ j.val), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  have hbound : (∑ j : Fin N, if 2 ^ j.val ≤ w v then (2 ^ j.val : ℕ) else 0) ≤ 2 * w v := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if 2 ^ j ≤ w v then 2 ^ j else 0) N]
    exact dyadic_supported_sum N (w v)
  have hboundR : (∑ j : Fin N, if 2 ^ j.val ≤ w v then (2 : ℝ) ^ j.val else 0) ≤ 2 * (w v : ℝ) := by
    exact_mod_cast hbound
  apply le_trans ?_ hboundR
  apply Finset.sum_le_sum
  intro j _
  by_cases hv : v ∈ S j
  · simp only [ite_eq_left hv, ite_eq_left (hS j v hv), le_refl]
  · simp only [ite_eq_right hv]
    split_ifs <;> positivity

theorem reciprocal_dyadic_sum (start N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (2 : ℝ) ^ (start + j)) ≤ 2 / (2 : ℝ) ^ start := by
  have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le N)
    (show 0 ≤ 1 / (2 : ℝ) ^ start by positivity)
  calc
    _ = (1 / (2 : ℝ) ^ start) * ∑ j ∈ Finset.range N, (1 / (2 : ℝ)) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add, div_pow]
      ring
    _ ≤ (1 / (2 : ℝ) ^ start) * 2 := h
    _ = _ := by ring

end Erdos911
