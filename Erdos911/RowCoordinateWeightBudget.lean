import Erdos911.RowCoordinateLogCounts

namespace Erdos911

/-- The event count is absorbed by the maximum event weight, leaving
the uniform per-row budget needed by the coordinate local lemma. -/
theorem row_coordinate_weight_sum_bound (q : ℕ) (hq : 2 ^ 32 ≤ q) :
    (dictionaryRowEventCount q : ℝ) * Real.exp (-(dictionaryLowDegree q : ℝ) / 128) ≤
      dictionaryRowWeightBudget q := by
  have hqpos : 0 < q := by norm_num at hq; omega
  have hqp : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hwp := dictionaryWordLength_pos q
  have hNpos : 0 < dictionaryRowEventCount q := by
    unfold dictionaryRowEventCount dictionaryConflictDegree dictionaryLowDegree dictionaryPatternCount
      dictionaryLeftSize dictionaryDegreeCharge dictionaryBadLimit
    positivity
  have hNposR : (0 : ℝ) < dictionaryRowEventCount q := by exact_mod_cast hNpos
  have hN : (dictionaryRowEventCount q : ℝ) ≤ Real.exp ((q : ℝ) ^ 46) := by
    calc
      _ = Real.exp (Real.log (dictionaryRowEventCount q)) := (Real.exp_log hNposR).symm
      _ ≤ _ := Real.exp_le_exp.mpr (row_coordinate_event_log_bound q hq)
  have hD : (dictionaryLowDegree q : ℝ) / 128 = (q : ℝ) ^ 50 / 16 := by
    unfold dictionaryLowDegree dictionaryDegreeCharge
    push_cast
    ring
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast (show 3 ≤ q by norm_num at hq; omega)
  have hq4 : (32 : ℝ) ≤ (q : ℝ) ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hq3 4
    norm_num at hh
    linarith only [hh]
  have hscale := mul_le_mul_of_nonneg_right hq4 (show 0 ≤ (q : ℝ) ^ 46 by positivity)
  have heq50 : (q : ℝ) ^ 4 * (q : ℝ) ^ 46 = (q : ℝ) ^ 50 := by ring
  rw [heq50] at hscale
  have hneg : (q : ℝ) ^ 46 - (q : ℝ) ^ 50 / 16 ≤ -(q : ℝ) ^ 46 := by linarith only [hscale]
  have hηform : dictionaryRowWeightBudget q = 1 / (8192 * (q : ℝ) ^ 89) := by
    unfold dictionaryRowWeightBudget dictionaryLeftSize dictionaryDegreeCharge
    push_cast
    field_simp
  have hηpos : 0 < dictionaryRowWeightBudget q := by rw [hηform]; positivity
  have hlog8192 : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    norm_num
  have hηlog : Real.log (dictionaryRowWeightBudget q) = -(13 * Real.log 2 + 89 * Real.log q) := by
    rw [hηform, Real.log_div (by norm_num) (by positivity), Real.log_one,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlog8192]
    ring
  have hlogq : Real.log q ≤ (q : ℝ) := (Real.log_le_sub_one_of_pos hqp).trans (by linarith)
  have hq102 : (102 : ℝ) ≤ q := by exact_mod_cast (show 102 ≤ q by norm_num at hq; omega)
  have hp45 : (102 : ℝ) ≤ (q : ℝ) ^ 45 := hq102.trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hq1 (by norm_num : 1 ≤ 45))
  have hq46 := mul_le_mul_of_nonneg_right hp45 hqp.le
  have hηbound : -(q : ℝ) ^ 46 ≤ Real.log (dictionaryRowWeightBudget q) := by
    rw [hηlog]
    nlinarith only [hq46, hlogq, dictionary_log_two_bounds.2, hq1]
  have hDneg : -(dictionaryLowDegree q : ℝ) / 128 = -(q : ℝ) ^ 50 / 16 := by linarith only [hD]
  rw [hDneg]
  calc
    _ ≤ Real.exp ((q : ℝ) ^ 46) * Real.exp (-(q : ℝ) ^ 50 / 16) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ = Real.exp ((q : ℝ) ^ 46 - (q : ℝ) ^ 50 / 16) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(q : ℝ) ^ 46) := Real.exp_le_exp.mpr hneg
    _ ≤ Real.exp (Real.log (dictionaryRowWeightBudget q)) := Real.exp_le_exp.mpr hηbound
    _ = dictionaryRowWeightBudget q := Real.exp_log hηpos

end Erdos911
