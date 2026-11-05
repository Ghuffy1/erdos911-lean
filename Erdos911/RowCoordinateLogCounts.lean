import Erdos911.RowCoordinateParameters
import Erdos911.DictionaryLogBounds

namespace Erdos911

theorem dictionary_conflict_log_bound (q : ℕ) (hq : 1 ≤ q) :
    Real.log (dictionaryConflictDegree q) ≤ 128 * (q : ℝ) ^ 2 := by
  have hqpos : 0 < q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hlog2 := dictionary_log_two_bounds.2
  have hlogq : Real.log q ≤ (q : ℝ) := (Real.log_le_sub_one_of_pos hqp).trans (by linarith)
  have hp20 : (1 : ℝ) ≤ (q : ℝ) ^ 20 := one_le_pow₀ hqR
  have hsmall : Real.log ((q : ℝ) ^ 20 + 1) ≤ 1 + 20 * (q : ℝ) := by
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (q : ℝ) ^ 20 + 1)
      (show (q : ℝ) ^ 20 + 1 ≤ 2 * (q : ℝ) ^ 20 by linarith only [hp20])
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
    norm_num at hh
    nlinarith only [hh, hlog2, hlogq]
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
  rw [hRform, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  have hm := mul_le_mul_of_nonneg_left hsmall hqp.le
  have hq2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith only [hqR]
  nlinarith only [hm, hlog128, hlogq, hq2, hqR]

theorem dictionary_word_log_bound (q : ℕ) (hq : 1 ≤ q) :
    Real.log (dictionaryWordLength q) ≤ 2 * (q : ℝ) := by
  obtain ⟨hloglo, hloghi⟩ := dictionary_log_two_bounds
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let a := Real.exp (Real.log 2 * q / 16)
  have ha : 1 ≤ a := by apply Real.one_le_exp_iff.mpr; positivity
  have hell : (dictionaryWordLength q : ℝ) ≤ 2 * a := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ a by linarith only [ha])
    change (dictionaryWordLength q : ℝ) < a + 1 at hh
    linarith only [hh, ha]
  have hp : (0 : ℝ) < dictionaryWordLength q := by exact_mod_cast dictionaryWordLength_pos q
  have hh := Real.log_le_log hp hell
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at hh
  have hmul := mul_le_mul_of_nonneg_right hloghi (show (0 : ℝ) ≤ q by positivity)
  nlinarith only [hh, hmul, hloghi, hqR]

/-- All event choices through a row have logarithmic count at most
q^46, below the q^50 decay in their largest local-lemma weight. -/
theorem row_coordinate_event_log_bound (q : ℕ) (hq : 2 ^ 32 ≤ q) :
    Real.log (dictionaryRowEventCount q) ≤ (q : ℝ) ^ 46 := by
  have hqpos : 0 < q := by norm_num at hq; omega
  have hq1 : 1 ≤ q := by omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqp : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hlog2 := dictionary_log_two_bounds.2
  have hlogq : Real.log q ≤ (q : ℝ) := (Real.log_le_sub_one_of_pos hqp).trans (by linarith)
  have hsmall (n : ℕ) : Real.log ((q : ℝ) ^ n + 1) ≤ 1 + n * (q : ℝ) := by
    have hp : (1 : ℝ) ≤ (q : ℝ) ^ n := one_le_pow₀ hqR
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (q : ℝ) ^ n + 1)
      (show (q : ℝ) ^ n + 1 ≤ 2 * (q : ℝ) ^ n by linarith only [hp])
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm := mul_le_mul_of_nonneg_left hlogq hn
    nlinarith only [hh, hlog2, hm]
  have hRpos : 0 < dictionaryConflictDegree q := by
    unfold dictionaryConflictDegree dictionaryPatternCount dictionaryLeftSize dictionaryLowDegree dictionaryDegreeCharge
    positivity
  have hRposR : (0 : ℝ) < dictionaryConflictDegree q := by exact_mod_cast hRpos
  have hWposR : (0 : ℝ) < dictionaryWordLength q := by exact_mod_cast dictionaryWordLength_pos q
  have hRform : dictionaryLowDegree q * (16 * dictionaryPatternCount q * dictionaryDegreeCharge q) =
      dictionaryConflictDegree q := by unfold dictionaryConflictDegree; ring
  have hform : dictionaryRowEventCount q = (dictionaryLeftSize q + 1) * (dictionaryBadLimit q + 1) *
      dictionaryConflictDegree q ^ (2 * dictionaryLeftSize q + 1) * dictionaryWordLength q ^ dictionaryBadLimit q := by
    unfold dictionaryRowEventCount
    rw [pow_succ]
    calc
      _ = (dictionaryLeftSize q + 1) * (dictionaryBadLimit q + 1) *
          (dictionaryLowDegree q * (16 * dictionaryPatternCount q * dictionaryDegreeCharge q)) *
          dictionaryConflictDegree q ^ (2 * dictionaryLeftSize q) *
          dictionaryWordLength q ^ dictionaryBadLimit q := by ring
      _ = _ := by rw [hRform]; ring
  have hreal : (dictionaryRowEventCount q : ℝ) = ((q : ℝ) ^ 20 + 1) * ((q : ℝ) ^ 43 + 1) *
      (dictionaryConflictDegree q : ℝ) ^ (2 * dictionaryLeftSize q + 1) *
        (dictionaryWordLength q : ℝ) ^ dictionaryBadLimit q := by
    rw [hform]
    simp only [dictionaryLeftSize, dictionaryBadLimit, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  rw [hreal, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  have hA := hsmall 20
  have hJ := hsmall 43
  have hR := mul_le_mul_of_nonneg_left (dictionary_conflict_log_bound q hq1)
    (show (0 : ℝ) ≤ 2 * (q : ℝ) ^ 20 + 1 by positivity)
  have hW := mul_le_mul_of_nonneg_left (dictionary_word_log_bound q hq1)
    (show (0 : ℝ) ≤ (q : ℝ) ^ 43 by positivity)
  have hp2 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 44 := pow_le_pow_right₀ hqR (by norm_num)
  have hp22 : (q : ℝ) ^ 22 ≤ (q : ℝ) ^ 44 := pow_le_pow_right₀ hqR (by norm_num)
  have hq44 : (q : ℝ) ≤ (q : ℝ) ^ 44 := by simpa only [pow_one] using pow_le_pow_right₀ hqR (by norm_num : 1 ≤ 44)
  have h144 : (1 : ℝ) ≤ (q : ℝ) ^ 44 := one_le_pow₀ hqR
  have hq2 : (512 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hh : (32 : ℝ) ≤ q := by exact_mod_cast (show 32 ≤ q by norm_num at hq; omega)
    nlinarith only [hh]
  have hlarge := mul_le_mul_of_nonneg_right hq2 (show 0 ≤ (q : ℝ) ^ 44 by positivity)
  have heq : (q : ℝ) ^ 2 * (q : ℝ) ^ 44 = (q : ℝ) ^ 46 := by ring
  rw [heq] at hlarge
  simp only [dictionaryLeftSize, dictionaryBadLimit, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at *
  nlinarith only [hA, hJ, hR, hW, hp2, hp22, hq44, h144, hlarge]

end Erdos911
