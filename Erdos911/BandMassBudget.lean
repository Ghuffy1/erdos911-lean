import Erdos911.DyadicBudget
import Erdos911.BandDegreeParameters
import Mathlib.Algebra.BigOperators.Intervals

namespace Erdos911

theorem reciprocal_dyadic_tail (start N : ℕ) :
    (∑ j ∈ Finset.range N, if start ≤ j then 1 / (2 : ℝ) ^ j else 0) ≤
      2 / (2 : ℝ) ^ start := by
  rw [← Finset.sum_filter]
  have hset : (Finset.range N).filter (fun j => start ≤ j) = Finset.Ico start N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.add_comm] using reciprocal_dyadic_sum start (N - start)

theorem reciprocal_active_band_budget (d N : ℕ) (hd : 0 < d) :
    (∑ j : Fin N, if d < 2 * 2 ^ j.val then 1 / (2 : ℝ) ^ j.val else 0) ≤
      4 / d := by
  have hstart (j : ℕ) (hj : d < 2 * 2 ^ j) : Nat.log 2 d ≤ j := by
    have hlt : d < 2 ^ (j + 1) := by simpa only [pow_succ, Nat.mul_comm] using hj
    have h := Nat.log_lt_of_lt_pow hd.ne' hlt
    omega
  have hsum : (∑ j : Fin N, if d < 2 * 2 ^ j.val then 1 / (2 : ℝ) ^ j.val else 0) ≤
      ∑ j : Fin N, if Nat.log 2 d ≤ j.val then 1 / (2 : ℝ) ^ j.val else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : d < 2 * 2 ^ j.val
    · simp only [ite_eq_left hj, ite_eq_left (hstart j.val hj), le_refl]
    · simp only [ite_eq_right hj]
      split_ifs <;> positivity
  have htail : (∑ j : Fin N, if Nat.log 2 d ≤ j.val then 1 / (2 : ℝ) ^ j.val else 0) ≤
      2 / (2 : ℝ) ^ Nat.log 2 d := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => if Nat.log 2 d ≤ j then 1 / (2 : ℝ) ^ j else 0) N]
    exact reciprocal_dyadic_tail (Nat.log 2 d) N
  apply (hsum.trans htail).trans
  have hden : (d : ℝ) ≤ 2 * (2 : ℝ) ^ Nat.log 2 d := by
    exact_mod_cast (dyadicFloor_bounds d hd).2.le
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 d)
    (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  nlinarith only [hden]

/-- The reciprocal normalized degrees have a geometric budget, with no
dependence on the number of bands. -/
theorem reciprocal_normalized_band_budget (d N : ℕ) (hd : 0 < d)
    (hq : ∀ j : Fin N, d < 2 * 2 ^ j.val → 131072 ≤ 2 ^ j.val) :
    (∑ j : Fin N, if d < 2 * 2 ^ j.val then
      1 / (bandDegree (2 ^ j.val) : ℝ) else 0) ≤ 524288 / d := by
  have hsum : (∑ j : Fin N, if d < 2 * 2 ^ j.val then
      1 / (bandDegree (2 ^ j.val) : ℝ) else 0) ≤
      131072 * ∑ j : Fin N, if d < 2 * 2 ^ j.val then 1 / (2 : ℝ) ^ j.val else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : d < 2 * 2 ^ j.val
    · simp only [ite_eq_left hj]
      obtain ⟨hd', _, hq', _⟩ := bandDegree_bounds (2 ^ j.val) (hq j hj)
      have hpos : (0 : ℝ) < bandDegree (2 ^ j.val) := by exact_mod_cast hd'
      have hqR : (2 : ℝ) ^ j.val ≤ 131072 * bandDegree (2 ^ j.val) := by exact_mod_cast hq'
      rw [mul_one_div]
      apply (div_le_div_iff₀ hpos (by positivity : (0 : ℝ) < (2 : ℝ) ^ j.val)).mpr
      simpa only [one_mul] using hqR
    · simp only [ite_eq_right hj, mul_zero, le_refl]
  have h := mul_le_mul_of_nonneg_left (reciprocal_active_band_budget d N hd)
    (by norm_num : (0 : ℝ) ≤ 131072)
  calc
    _ ≤ 131072 * (4 / (d : ℝ)) := hsum.trans h
    _ = 524288 / d := by ring

end Erdos911
