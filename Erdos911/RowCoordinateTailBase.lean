import Erdos911.RowCoordinateParameters

namespace Erdos911

/-- The exponential number of coordinates dominates the polynomial
factors in the row-subset tail, with an explicit large-q threshold. -/
theorem row_coordinate_tail_base (q : ℕ) (hq : 2 ^ 32 ≤ q) :
    16 * Real.exp 1 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q *
      dictionaryBadLimit q / dictionaryWordLength q ≤ Real.exp (-(q : ℝ) / 64) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by norm_num at hq; omega)
  have hq0 := hqp.le
  have hs : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (q : ℝ) ^ 2 = q := Real.sq_sqrt hq0
  have hqbig : (4294967296 : ℝ) ≤ q := by exact_mod_cast hq
  have hslo : (65536 : ℝ) ≤ Real.sqrt (q : ℝ) := by nlinarith only [hs, hs2, hqbig]
  have hlogq : Real.log q ≤ 2 * Real.sqrt (q : ℝ) := by
    have hh := Real.log_le_rpow_div hq0 (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    linarith only [hh]
  have hmul := mul_le_mul_of_nonneg_right hslo hs
  have hpoly : 5 + 133 * Real.log q ≤ (q : ℝ) / 64 := by
    nlinarith only [hlogq, hmul, hs2, hslo]
  obtain ⟨hloglo, hloghi⟩ := dictionary_log_two_bounds
  have hellp : (0 : ℝ) < dictionaryWordLength q := by exact_mod_cast dictionaryWordLength_pos q
  have hlogell : Real.log 2 * q / 16 ≤ Real.log (dictionaryWordLength q) := by
    have hh := Real.log_le_log (Real.exp_pos (Real.log 2 * q / 16))
      (Nat.le_ceil (Real.exp (Real.log 2 * q / 16)))
    rw [Real.log_exp] at hh
    exact hh
  have hqlog := mul_le_mul_of_nonneg_right hloglo hq0
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hform : 16 * Real.exp 1 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q *
      dictionaryBadLimit q / dictionaryWordLength q =
      16 * Real.exp 1 * (q : ℝ) ^ 133 / dictionaryWordLength q := by
    unfold dictionaryLeftSize dictionaryDegreeCharge dictionaryBadLimit
    push_cast
    ring
  rw [hform]
  have hpos : 0 < 16 * Real.exp 1 * (q : ℝ) ^ 133 / dictionaryWordLength q := by positivity
  have hlog : Real.log (16 * Real.exp 1 * (q : ℝ) ^ 133 / dictionaryWordLength q) ≤ -(q : ℝ) / 64 := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_exp, Real.log_pow, hlog16]
    norm_num
    nlinarith only [hpoly, hlogell, hqlog, hloghi]
  calc
    _ = Real.exp (Real.log (16 * Real.exp 1 * (q : ℝ) ^ 133 / dictionaryWordLength q)) :=
      (Real.exp_log hpos).symm
    _ ≤ Real.exp (-(q : ℝ) / 64) := Real.exp_le_exp.mpr hlog

end Erdos911
