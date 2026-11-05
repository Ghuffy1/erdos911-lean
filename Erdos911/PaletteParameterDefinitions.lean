import Erdos911.PaletteLogCard
import Erdos911.SparsePaletteRamsey

namespace Erdos911

def sparsePaletteConstant : ℝ := 1099511627776

noncomputable def paletteDensityLog (Λ : ℝ) (Δ : ℕ) : ℝ := 1 + Real.log (128 * Λ * Δ)

noncomputable def paletteDegreeCutoff (Λ : ℝ) (Δ : ℕ) : ℕ := Nat.ceil (128 * Λ * Δ)

structure ExplicitSparsePalette (d Δ L : ℕ) (Λ σ : ℝ) where
  D : ℕ
  k : ℕ
  p : ℝ
  gap : ℝ
  large_cutoff : 1000 ≤ D
  large_reciprocal : 2 ≤ k
  multiplier_le : Λ ≤ D
  probability_nonneg : 0 ≤ p
  probability_le_one : p ≤ 1
  gap_nonneg : 0 ≤ gap
  collision_margin : 256 * σ ≤ (k : ℝ) * d
  cutoff_bound : 128 * Λ * Δ ≤ (D : ℝ)
  red_scale : 256 * Real.log D ≤ p * d
  blue_base : 16 * Real.exp 1 * p ≤ Real.exp (-gap)
  entropy_bound : Real.log (Fintype.card (CollisionPalette D L k)) + 2 * Real.log Δ ≤
    (d : ℝ) * gap / 64
  geometric_bound : 128 * Real.log 2 ≤ (d : ℝ) * gap
  component_bound : Real.log L + Real.log 1000 ≤ (d : ℝ) ^ 2 * gap / 512

theorem palette_log_cutoff_bounds (Λ : ℝ) (Δ : ℕ) (hΛ : 1 ≤ Λ) (hΔ : 1 ≤ Δ) :
    1 ≤ paletteDensityLog Λ Δ ∧
      128 * Λ * Δ ≤ (paletteDegreeCutoff Λ Δ : ℝ) ∧
      Λ ≤ (paletteDegreeCutoff Λ Δ : ℝ) ∧
      (Δ : ℝ) ≤ paletteDegreeCutoff Λ Δ ∧
      Real.log (paletteDegreeCutoff Λ Δ) ≤ paletteDensityLog Λ Δ ∧
      Real.log ((paletteDegreeCutoff Λ Δ : ℝ) + 1) ≤ 2 * paletteDensityLog Λ Δ ∧
      Real.log Δ ≤ paletteDensityLog Λ Δ := by
  let x : ℝ := 128 * Λ * Δ
  let D := paletteDegreeCutoff Λ Δ
  have hΔR : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hx : 128 ≤ x := by
    have h := one_le_mul_of_one_le_of_one_le hΛ hΔR
    dsimp only [x]
    nlinarith only [h]
  have hxp : 0 < x := by linarith
  have hDlo : x ≤ (D : ℝ) := Nat.le_ceil _
  have hDup : (D : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hxp.le).le
  have hDpos : (0 : ℝ) < D := hxp.trans_le hDlo
  have hDtwice : (D : ℝ) ≤ 2 * x := by linarith
  have hDthree : (D : ℝ) + 1 ≤ 3 * x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogD := Real.log_le_log hDpos hDtwice
  have hlogD1 := Real.log_le_log (by positivity : 0 < (D : ℝ) + 1) hDthree
  rw [Real.log_mul (by norm_num) hxp.ne'] at hlogD hlogD1
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hΛx : Λ ≤ x := by
    have h := mul_le_mul_of_nonneg_left hΔR (show 0 ≤ Λ by linarith)
    dsimp only [x]
    nlinarith only [h, hΛ]
  have hΔx : (Δ : ℝ) ≤ x := by
    have h := mul_le_mul_of_nonneg_right hΛ (Nat.cast_nonneg (α := ℝ) Δ)
    dsimp only [x]
    nlinarith only [h, Nat.cast_nonneg (α := ℝ) Δ]
  have hlogΔ := Real.log_le_log (show (0 : ℝ) < Δ by linarith) hΔx
  change 1 ≤ 1 + Real.log x ∧ x ≤ (D : ℝ) ∧ Λ ≤ D ∧ (Δ : ℝ) ≤ D ∧
    Real.log D ≤ 1 + Real.log x ∧ Real.log ((D : ℝ) + 1) ≤ 2 * (1 + Real.log x) ∧
    Real.log Δ ≤ 1 + Real.log x
  exact ⟨by linarith, hDlo, hΛx.trans hDlo, hΔx.trans hDlo,
    by linarith, by linarith, by linarith⟩

end Erdos911
