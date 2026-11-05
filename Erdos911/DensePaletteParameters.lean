import Erdos911.BoundedPaletteParameters

namespace Erdos911

/-- Passing to a sixteen-times-higher degree core preserves the
quantitative bounded-component hypotheses at the rescaled edge budget. -/
theorem bounded_palette_dense_parameters (d Δ L : ℕ) (Λ : ℝ)
    (hd : 1 ≤ d) (hsΔ : 16 * d ≤ Δ) (hΛ : 1 ≤ Λ)
    (hscale : Real.exp 1 * boundedPaletteConstant * paletteDensityLog Λ Δ ≤ d)
    (horder : Real.log L ≤ (d : ℝ) / 8192 *
      Real.log ((d : ℝ) / (boundedPaletteConstant * paletteDensityLog Λ Δ))) :
    1 ≤ (Δ : ℝ) * Λ / (2 * d) ∧
      Real.exp 1 * boundedPaletteConstant *
        paletteDensityLog ((Δ : ℝ) * Λ / (2 * d)) Δ ≤ (16 * d : ℕ) ∧
      Real.log L ≤ ((16 * d : ℕ) : ℝ) / 8192 *
        Real.log (((16 * d : ℕ) : ℝ) / (boundedPaletteConstant *
          paletteDensityLog ((Δ : ℝ) * Λ / (2 * d)) Δ)) := by
  let Λ' := (Δ : ℝ) * Λ / (2 * d)
  let T := paletteDensityLog Λ Δ
  let T' := paletteDensityLog Λ' Δ
  let A := boundedPaletteConstant * T
  let A' := boundedPaletteConstant * T'
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hΔR : (16 : ℝ) * d ≤ Δ := by exact_mod_cast hsΔ
  have hdΔ : d ≤ Δ := by omega
  have hΔ : 1 ≤ Δ := hd.trans hdΔ
  have hΔp : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hΛ' : 1 ≤ Λ' := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (d : ℝ))).mpr
    have h := mul_le_mul_of_nonneg_left hΛ hΔp.le
    nlinarith only [h, hΔR, hdR]
  have hΛ'up : Λ' ≤ 128 * Λ ^ 2 * Δ := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (d : ℝ))).mpr
    have hsq : Λ ≤ Λ ^ 2 := by nlinarith only [hΛ]
    have hm₁ := mul_le_mul_of_nonneg_right hsq hΔp.le
    have hm₂ := mul_le_mul_of_nonneg_left hdR (show 0 ≤ Λ ^ 2 * (Δ : ℝ) by positivity)
    nlinarith only [hm₁, hm₂]
  have hT := (palette_log_cutoff_bounds Λ Δ hΛ hΔ).1
  have hT' := (palette_log_cutoff_bounds Λ' Δ hΛ' hΔ).1
  have hTup : T' ≤ 2 * T := palette_density_log_le_double Λ Λ' Δ hΛ hΔ hΛ' hΛ'up
  have hAp : 0 < A := by dsimp only [A, boundedPaletteConstant]; positivity
  have hA'p : 0 < A' := by dsimp only [A', boundedPaletteConstant]; positivity
  have hA : A' ≤ 2 * A := by
    dsimp only [A, A', boundedPaletteConstant]
    nlinarith only [hTup]
  have hs : Real.exp 1 * A' ≤ (16 * d : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hA (Real.exp_pos 1).le
    change Real.exp 1 * boundedPaletteConstant * T ≤ d at hscale
    dsimp only [A] at hm
    nlinarith only [hm, hscale, hdR]
  have hratio : (d : ℝ) / A ≤ (16 * d : ℝ) / A' := by
    apply (div_le_div_iff₀ hAp hA'p).mpr
    have hm := mul_le_mul_of_nonneg_left hA hdp.le
    nlinarith only [hm, mul_nonneg hdp.le hAp.le]
  have hlogup := Real.log_le_log (div_pos hdp hAp) hratio
  have hlog := (bounded_palette_scale_large d Δ Λ hΛ hΔ hscale).2
  change 1 ≤ Real.log ((d : ℝ) / A) at hlog
  have hcoef : (d : ℝ) / 8192 ≤ (16 * d : ℝ) / 8192 := by linarith only [hdR]
  have hm₁ := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ Real.log ((d : ℝ) / A) by linarith)
  have hm₂ := mul_le_mul_of_nonneg_left hlogup (show 0 ≤ (16 * d : ℝ) / 8192 by positivity)
  have ho : Real.log L ≤ (16 * d : ℝ) / 8192 * Real.log ((16 * d : ℝ) / A') := by
    change Real.log L ≤ (d : ℝ) / 8192 * Real.log ((d : ℝ) / A) at horder
    exact horder.trans (hm₁.trans hm₂)
  refine ⟨hΛ', ?_, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, A', T', mul_assoc] using hs
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using ho

end Erdos911
