import Erdos911.DictionaryLogBounds
import Erdos911.DictionaryTailParameters

namespace Erdos911

/-- The complete union bound over all partial-label tests is below 1/8,
uniformly in the number, size and diversity of target blocks. -/
theorem dictionary_failure_budget (q : ℕ) (hq : 65536 ≤ q) :
    (dictionaryTestCount q : ℝ) *
      (8 * (dictionaryWordLength q : ℝ) ^ 2 * (1 / 2 : ℝ) ^ dictionaryRowMinimum q) ^
        dictionaryBadLimit q ≤ 1 / 8 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqN : 1 ≤ q := by omega
  have hlog := dictionary_test_log_bound q hqN
  have hTpos : (0 : ℝ) < dictionaryTestCount q := by
    unfold dictionaryTestCount
    positivity
  have hT : (dictionaryTestCount q : ℝ) ≤ Real.exp (131 * (q : ℝ) ^ 42) := by
    calc
      _ = Real.exp (Real.log (dictionaryTestCount q)) := (Real.exp_log hTpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  have hbase := dictionary_tail_base_bound q hq
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    8 * (dictionaryWordLength q : ℝ) ^ 2 * (1 / 2 : ℝ) ^ dictionaryRowMinimum q)
    hbase (dictionaryBadLimit q)
  have hexp : Real.exp (-(q : ℝ) / 8) ^ dictionaryBadLimit q = Real.exp (-(q : ℝ) ^ 44 / 8) := by
    rw [← Real.exp_nat_mul]
    congr 1
    unfold dictionaryBadLimit
    push_cast
    ring
  rw [hexp] at hpow
  have hm := mul_le_mul hT hpow (by positivity) (by positivity)
  have hq2 : (2048 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hh : (64 : ℝ) ≤ q := by exact_mod_cast (show 64 ≤ q by omega)
    nlinarith only [hh]
  have hp42 : (1 : ℝ) ≤ (q : ℝ) ^ 42 := one_le_pow₀ hq1
  have hscaled := mul_le_mul_of_nonneg_right hq2 (show 0 ≤ (q : ℝ) ^ 42 by positivity)
  have heq : (q : ℝ) ^ 2 * (q : ℝ) ^ 42 = (q : ℝ) ^ 44 := by ring
  rw [heq] at hscaled
  have hnegative : 131 * (q : ℝ) ^ 42 - (q : ℝ) ^ 44 / 8 ≤ -3 * Real.log 2 := by
    nlinarith only [hscaled, hp42, dictionary_log_two_bounds.2]
  have hfinal : Real.exp (-3 * Real.log 2) = (1 / 8 : ℝ) := by
    have hthree : Real.exp (3 * Real.log 2) = (Real.exp (Real.log 2)) ^ 3 := by
      simpa using Real.exp_nat_mul (Real.log 2) 3
    rw [neg_mul, Real.exp_neg, hthree]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    _ ≤ Real.exp (131 * (q : ℝ) ^ 42) * Real.exp (-(q : ℝ) ^ 44 / 8) := hm
    _ = Real.exp (131 * (q : ℝ) ^ 42 - (q : ℝ) ^ 44 / 8) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-3 * Real.log 2) := Real.exp_le_exp.mpr hnegative
    _ = 1 / 8 := hfinal

end Erdos911
