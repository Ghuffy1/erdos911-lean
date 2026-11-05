import Erdos911.CollisionSafePalette

namespace Erdos911

theorem collisionPalette_log_card_le (D L k : ℕ) (hL : 1 ≤ L) :
    Real.log (Fintype.card (CollisionPalette D L k)) ≤
      Real.log L + (12 * (k : ℝ) + 2) * Real.log ((D : ℝ) + 1) := by
  have hbase : 1 ≤ D + 1 := by omega
  have hpower : 1 ≤ (D + 1) ^ (12 * k) := Nat.one_le_pow _ _ hbase
  have hprod : 1 ≤ L * (D + 1) ^ (12 * k) := one_le_mul_of_one_le_of_one_le hL hpower
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hDp : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hQp : (0 : ℝ) < (D : ℝ) * ((D : ℝ) + 1) + 1 := by positivity
  have hQ : (D : ℝ) * ((D : ℝ) + 1) + 1 ≤ ((D : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have hlogQ : Real.log ((D : ℝ) * ((D : ℝ) + 1) + 1) ≤ 2 * Real.log ((D : ℝ) + 1) := by
    have h := Real.log_le_log hQp hQ
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  rw [collisionPalette_card, max_eq_right hprod]
  push_cast
  rw [Real.log_mul (mul_pos hLp (pow_pos hDp _)).ne' hQp.ne',
    Real.log_mul hLp.ne' (pow_pos hDp _).ne', Real.log_pow]
  push_cast
  nlinarith only [hlogQ]

end Erdos911
