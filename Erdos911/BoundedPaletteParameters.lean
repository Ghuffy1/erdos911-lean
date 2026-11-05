import Erdos911.QuantitativeSparsePalette

namespace Erdos911

def boundedPaletteConstant : ℝ := 281474976710656

theorem palette_density_log_le_double (Λ Λ' : ℝ) (Δ : ℕ)
    (hΛ : 1 ≤ Λ) (hΔ : 1 ≤ Δ) (hΛ' : 1 ≤ Λ')
    (hup : Λ' ≤ 128 * Λ ^ 2 * Δ) :
    paletteDensityLog Λ' Δ ≤ 2 * paletteDensityLog Λ Δ := by
  have hΔp : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hΛp : 0 < Λ := by linarith
  have hΛ'p : 0 < Λ' := by linarith
  have hmul := mul_le_mul_of_nonneg_right hup (show 0 ≤ 128 * (Δ : ℝ) by positivity)
  have hx : 128 * Λ' * Δ ≤ (128 * Λ * Δ) ^ 2 := by nlinarith only [hmul]
  have hlog := Real.log_le_log (show 0 < 128 * Λ' * Δ by positivity) hx
  rw [Real.log_pow] at hlog
  dsimp only [paletteDensityLog]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]

theorem bounded_palette_scale_large (d Δ : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (hΔ : 1 ≤ Δ)
    (hscale : Real.exp 1 * boundedPaletteConstant * paletteDensityLog Λ Δ ≤ d) :
    281474976710656 ≤ d ∧ 1 ≤ Real.log
      ((d : ℝ) / (boundedPaletteConstant * paletteDensityLog Λ Δ)) := by
  have hT := (palette_log_cutoff_bounds Λ Δ hΛ hΔ).1
  have hB : boundedPaletteConstant = 281474976710656 := rfl
  have hBT : 0 < boundedPaletteConstant * paletteDensityLog Λ Δ := by
    rw [hB]
    positivity
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right he hBT.le
  have hdB : (281474976710656 : ℝ) ≤ d := by nlinarith only [hT, hB, hmul, hscale]
  have hratio : Real.exp 1 ≤ (d : ℝ) / (boundedPaletteConstant * paletteDensityLog Λ Δ) := by
    apply (le_div_iff₀ hBT).mpr
    nlinarith only [hscale]
  have hlog := Real.log_le_log (Real.exp_pos 1) hratio
  rw [Real.log_exp] at hlog
  exact ⟨by exact_mod_cast hdB, hlog⟩

/-- The low-degree residual can use the sparse theorem at a quarter of
the original minimum degree without losing the order hypothesis. -/
theorem bounded_palette_sparse_parameters (d Δ L : ℕ) (Λ : ℝ)
    (hd : 1 ≤ d) (hdΔ : d ≤ Δ) (hΛ : 1 ≤ Λ)
    (hscale : Real.exp 1 * boundedPaletteConstant * paletteDensityLog Λ Δ ≤ d)
    (horder : Real.log L ≤ (d : ℝ) / 8192 *
      Real.log ((d : ℝ) / (boundedPaletteConstant * paletteDensityLog Λ Δ))) :
    1 ≤ d / 4 ∧ (16 * d : ℝ) ≤ 128 * (d / 4 : ℕ) ∧
      Real.exp 1 * sparsePaletteConstant * paletteDensityLog (4 * Λ) Δ ≤ (d / 4 : ℕ) ∧
      Real.log L ≤ ((d / 4 : ℕ) : ℝ) / 1280 *
        Real.log (((d / 4 : ℕ) : ℝ) /
          (sparsePaletteConstant * paletteDensityLog (4 * Λ) Δ)) := by
  let T := paletteDensityLog Λ Δ
  let T' := paletteDensityLog (4 * Λ) Δ
  let A := boundedPaletteConstant * T
  let A' := sparsePaletteConstant * T'
  let q := d / 4
  obtain ⟨hdlarge, hlog⟩ := bounded_palette_scale_large d Δ Λ hΛ (hd.trans hdΔ) hscale
  have hdq : d ≤ 5 * q := by dsimp only [q]; omega
  have hq : 1 ≤ q := by dsimp only [q]; omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hdqR : (d : ℝ) ≤ 5 * q := by exact_mod_cast hdq
  have hT := (palette_log_cutoff_bounds Λ Δ hΛ (hd.trans hdΔ)).1
  have hΛ' : 1 ≤ 4 * Λ := by linarith
  have hT' := (palette_log_cutoff_bounds (4 * Λ) Δ hΛ' (hd.trans hdΔ)).1
  have hΔR : (1 : ℝ) ≤ Δ := by exact_mod_cast (hd.trans hdΔ)
  have hproduct : Λ ≤ Λ ^ 2 * Δ := by
    have hsq : Λ ≤ Λ ^ 2 := by nlinarith only [hΛ]
    have hm := mul_le_mul_of_nonneg_left hΔR (sq_nonneg Λ)
    nlinarith only [hsq, hm]
  have hTup : T' ≤ 2 * T := palette_density_log_le_double Λ (4 * Λ) Δ hΛ
    (hd.trans hdΔ) hΛ' (by nlinarith only [hproduct, hΛ])
  have hAp : 0 < A := by dsimp only [A, boundedPaletteConstant]; positivity
  have hA'p : 0 < A' := by dsimp only [A', sparsePaletteConstant]; positivity
  have hA : 5 * A' ≤ A := by
    dsimp only [A, A', boundedPaletteConstant, sparsePaletteConstant]
    nlinarith only [hTup, hT]
  have hscale' : Real.exp 1 * A' ≤ (q : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hA (Real.exp_pos 1).le
    change Real.exp 1 * boundedPaletteConstant * T ≤ d at hscale
    dsimp only [A] at hmul
    nlinarith only [hmul, hscale, hdqR]
  have hratio : (d : ℝ) / A ≤ (q : ℝ) / A' := by
    apply (div_le_div_iff₀ hAp hA'p).mpr
    have h₁ := mul_le_mul_of_nonneg_left hA hdR.le
    have h₂ := mul_le_mul_of_nonneg_right hdqR hAp.le
    nlinarith only [h₁, h₂]
  have hlogup := Real.log_le_log (div_pos hdR hAp) hratio
  have hlog0 : 0 ≤ Real.log ((d : ℝ) / A) := by
    change 1 ≤ Real.log ((d : ℝ) / A) at hlog
    linarith only [hlog]
  have hcoef : (d : ℝ) / 8192 ≤ (q : ℝ) / 1280 := by linarith only [hdqR]
  have hm₁ := mul_le_mul_of_nonneg_right hcoef hlog0
  have hm₂ := mul_le_mul_of_nonneg_left hlogup (show 0 ≤ (q : ℝ) / 1280 by positivity)
  have horder' : Real.log L ≤ (q : ℝ) / 1280 * Real.log ((q : ℝ) / A') := by
    change Real.log L ≤ (d : ℝ) / 8192 * Real.log ((d : ℝ) / A) at horder
    exact horder.trans (hm₁.trans hm₂)
  refine ⟨hq, ?_, ?_, horder'⟩
  · change (16 * d : ℝ) ≤ 128 * (q : ℝ)
    linarith only [hdqR]
  · simpa only [A', T', mul_assoc] using hscale'

end Erdos911
