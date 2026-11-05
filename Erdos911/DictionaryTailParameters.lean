import Erdos911.DictionaryParameters

namespace Erdos911

/-- Exponential dictionary length dominates the uniform-row probability;
the floor in the row threshold and ceiling in the length are explicit. -/
theorem dictionary_tail_base_bound (q : ℕ) (hq : 65536 ≤ q) :
    8 * (dictionaryWordLength q : ℝ) ^ 2 * (1 / 2 : ℝ) ^ dictionaryRowMinimum q ≤
      Real.exp (-(q : ℝ) / 8) := by
  obtain ⟨hloglo, hloghi⟩ := dictionary_log_two_bounds
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hq96 : (96 : ℝ) ≤ q := by exact_mod_cast (show 96 ≤ q by omega)
  let a := Real.exp (Real.log 2 * q / 16)
  have ha : 1 ≤ a := by
    apply Real.one_le_exp_iff.mpr
    positivity
  have hell : (dictionaryWordLength q : ℝ) ≤ 2 * a := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ a by linarith only [ha])
    change (dictionaryWordLength q : ℝ) < a + 1 at hh
    linarith only [hh, ha]
  have hellpos : (0 : ℝ) < dictionaryWordLength q := by
    have hh := Nat.le_ceil a
    change a ≤ (dictionaryWordLength q : ℝ) at hh
    linarith only [ha, hh]
  have hlogell : Real.log (dictionaryWordLength q) ≤ Real.log 2 + Real.log 2 * q / 16 := by
    have hh := Real.log_le_log hellpos hell
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at hh
    exact hh
  have hdiv : (q : ℝ) ≤ 2 * (dictionaryRowMinimum q : ℝ) + 1 := by
    exact_mod_cast (show q ≤ 2 * dictionaryRowMinimum q + 1 by unfold dictionaryRowMinimum; omega)
  have hlognonneg : 0 ≤ Real.log (2 : ℝ) := by linarith only [hloglo]
  have hm := mul_le_mul_of_nonneg_left hdiv hlognonneg
  have hqlog := mul_le_mul_of_nonneg_right hloglo hq0
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  let b : ℝ := 8 * (dictionaryWordLength q : ℝ) ^ 2 * (1 / 2 : ℝ) ^ dictionaryRowMinimum q
  have hb : 0 < b := by dsimp only [b]; positivity
  have hlogb : Real.log b ≤ -(q : ℝ) / 8 := by
    dsimp only [b]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow, hlog8, hloghalf]
    norm_num
    nlinarith only [hlogell, hm, hqlog, hloghi, hq96]
  calc
    b = Real.exp (Real.log b) := (Real.exp_log hb).symm
    _ ≤ Real.exp (-(q : ℝ) / 8) := Real.exp_le_exp.mpr hlogb

end Erdos911
