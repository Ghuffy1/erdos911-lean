import Erdos911.DictionaryParameters

namespace Erdos911

/-- The finite label and partial-map test counts have polynomial
logarithms, despite the unrestricted number of target blocks. -/
theorem dictionary_test_log_bound (q : ℕ) (hq : 1 ≤ q) :
    Real.log (dictionaryTestCount q) ≤ 131 * (q : ℝ) ^ 42 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : 0 < q := by omega
  have hqp : (0 : ℝ) < q := by linarith
  have hlog2 := dictionary_log_two_bounds.2
  have hlogq : Real.log q ≤ (q : ℝ) := (Real.log_le_sub_one_of_pos hqp).trans (by linarith)
  have hp20 : (1 : ℝ) ≤ (q : ℝ) ^ 20 := one_le_pow₀ hqR
  have hsmall : Real.log ((q : ℝ) ^ 20 + 1) ≤ 1 + 20 * (q : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (q : ℝ) ^ 20 + 1)
      (show (q : ℝ) ^ 20 + 1 ≤ 2 * (q : ℝ) ^ 20 by linarith only [hp20])
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
    norm_num at hh
    nlinarith only [hh, hlog2, hlogq]
  have hRpos : 0 < dictionaryConflictDegree q := by
    unfold dictionaryConflictDegree dictionaryPatternCount dictionaryLeftSize dictionaryLowDegree dictionaryDegreeCharge
    positivity
  have hRone : (1 : ℝ) ≤ dictionaryConflictDegree q := by exact_mod_cast hRpos
  have hRform : (dictionaryConflictDegree q : ℝ) =
      128 * ((q : ℝ) ^ 20 + 1) ^ q * (q : ℝ) ^ 100 := by
    unfold dictionaryConflictDegree dictionaryPatternCount dictionaryLeftSize dictionaryLowDegree dictionaryDegreeCharge
    push_cast
    ring
  have hlog128 : Real.log (128 : ℝ) ≤ 7 := by
    have hh : Real.log (128 : ℝ) = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    rw [hh]
    linarith only [hlog2]
  have hlogR : Real.log (dictionaryConflictDegree q) ≤ 128 * (q : ℝ) ^ 2 := by
    rw [hRform, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    have hm := mul_le_mul_of_nonneg_left hsmall hqp.le
    have hq2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith only [hqR]
    nlinarith only [hm, hlog128, hlogq, hq2, hqR]
  have hRnext : Real.log ((dictionaryConflictDegree q : ℝ) + 1) ≤ 129 * (q : ℝ) ^ 2 := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (dictionaryConflictDegree q : ℝ) + 1)
      (show (dictionaryConflictDegree q : ℝ) + 1 ≤ 2 * dictionaryConflictDegree q by linarith only [hRone])
    rw [Real.log_mul (by norm_num) (by positivity)] at hh
    have hp2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := one_le_pow₀ hqR
    nlinarith only [hh, hlog2, hlogR, hp2]
  have hLabelForm : (dictionaryLabelCount q : ℝ) + 1 =
      ((dictionaryConflictDegree q : ℝ) + 1) ^ (q ^ 20) + 2 := by
    unfold dictionaryLabelCount dictionaryLeftSize
    push_cast
    ring
  have hbase1 : (1 : ℝ) ≤ ((dictionaryConflictDegree q : ℝ) + 1) ^ (q ^ 20) :=
    one_le_pow₀ (by linarith only [hRone])
  have hlabel : Real.log ((dictionaryLabelCount q : ℝ) + 1) ≤ 131 * (q : ℝ) ^ 22 := by
    rw [hLabelForm]
    have hh := Real.log_le_log (by positivity : (0 : ℝ) <
      ((dictionaryConflictDegree q : ℝ) + 1) ^ (q ^ 20) + 2)
      (show ((dictionaryConflictDegree q : ℝ) + 1) ^ (q ^ 20) + 2 ≤
        3 * ((dictionaryConflictDegree q : ℝ) + 1) ^ (q ^ 20) by linarith only [hbase1])
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
    have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
      have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      norm_num at hl ⊢
      exact hl
    have hm := mul_le_mul_of_nonneg_left hRnext (show (0 : ℝ) ≤ (q : ℝ) ^ 20 by positivity)
    have hp22 : (1 : ℝ) ≤ (q : ℝ) ^ 22 := one_le_pow₀ hqR
    push_cast at hh
    have heq : (q : ℝ) ^ 20 * (129 * (q : ℝ) ^ 2) = 129 * (q : ℝ) ^ 22 := by ring
    rw [heq] at hm
    nlinarith only [hh, hm, hlog3, hp22]
  have hform : (dictionaryTestCount q : ℝ) = ((dictionaryLabelCount q : ℝ) + 1) ^ (q ^ 20) := by
    unfold dictionaryTestCount dictionaryLeftSize
    push_cast
    rfl
  rw [hform, Real.log_pow]
  push_cast
  have hm := mul_le_mul_of_nonneg_left hlabel (show (0 : ℝ) ≤ (q : ℝ) ^ 20 by positivity)
  convert hm using 1
  ring

end Erdos911
