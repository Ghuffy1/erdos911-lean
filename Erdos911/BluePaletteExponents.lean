import Erdos911.PaletteMapTails
import Erdos911.EntropyPartition

namespace Erdos911

theorem palette_blue_tail_exp {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d : ℕ) (hmin : ∀ v, d ≤ F.degree v)
    (S : Finset V) (p ℓ : ℝ) (hp : 0 ≤ p) (hℓ : 0 ≤ ℓ)
    (hbase : 16 * Real.exp 1 * p ≤ Real.exp (-ℓ)) :
    (16 * Real.exp 1 * p) ^ paletteMapThreshold F S ≤
      Real.exp (-(d : ℝ) * ℓ * S.card / 32) := by
  have hvolume : (d : ℝ) * S.card ≤ degreeVolume F S := by
    exact_mod_cast degreeVolume_minimum F d hmin S
  have hceil : (degreeVolume F S : ℝ) / 32 ≤ paletteMapThreshold F S := Nat.le_ceil _
  calc
    _ ≤ Real.exp (-ℓ) ^ paletteMapThreshold F S := pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp (-ℓ * paletteMapThreshold F S) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (show (d : ℝ) * S.card / 32 ≤ paletteMapThreshold F S by linarith) hℓ
      nlinarith only [h]

theorem palette_order_entropy_bound (D P d u : ℕ) (ℓ : ℝ)
    (hD : 1 ≤ D) (hP : 0 < P) (_hℓ : 0 ≤ ℓ)
    (hentropy : Real.log P + 2 * Real.log D ≤ (d : ℝ) * ℓ / 64) :
    (D : ℝ) ^ (2 * (u - 1)) * (P : ℝ) ^ u * Real.exp (-(d : ℝ) * ℓ * u / 32) ≤
      Real.exp (-(d : ℝ) * ℓ * u / 64) := by
  have hDP : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hPP : (0 : ℝ) < P := by exact_mod_cast hP
  have hpow : (D : ℝ) ^ (2 * (u - 1)) ≤ (D : ℝ) ^ (2 * u) :=
    pow_le_pow_right₀ (by exact_mod_cast hD) (by omega)
  have hformula : (D : ℝ) ^ (2 * u) * (P : ℝ) ^ u =
      Real.exp ((u : ℝ) * (Real.log P + 2 * Real.log D)) := by
    rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hPP]
    rw [show (u : ℝ) * (2 * Real.log D) = ((2 * u : ℕ) : ℝ) * Real.log D by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hDP]
    ring
  calc
    _ ≤ (D : ℝ) ^ (2 * u) * (P : ℝ) ^ u * Real.exp (-(d : ℝ) * ℓ * u / 32) := by
      gcongr
    _ = Real.exp ((u : ℝ) * (Real.log P + 2 * Real.log D) - (d : ℝ) * ℓ * u / 32) := by
      rw [hformula, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hentropy (Nat.cast_nonneg (α := ℝ) u)
      nlinarith only [h]

theorem palette_order_decay_split (d u : ℕ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hdu : d ≤ 4 * u) (hlog : 128 * Real.log 2 ≤ (d : ℝ) * ℓ) :
    Real.exp (-(d : ℝ) * ℓ * u / 64) ≤
      Real.exp (-(d : ℝ) ^ 2 * ℓ / 512) * (1 / 2 : ℝ) ^ u := by
  have hduR : (d : ℝ) ≤ 4 * u := by exact_mod_cast hdu
  have hdℓ : 0 ≤ (d : ℝ) * ℓ := mul_nonneg (Nat.cast_nonneg _) hℓ
  have h₁ := mul_le_mul_of_nonneg_left hduR hdℓ
  have h₂ := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) u)
  have hhalf : Real.exp (-Real.log (2 : ℝ)) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [← hhalf, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [h₁, h₂]

end Erdos911
