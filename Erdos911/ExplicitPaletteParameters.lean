import Erdos911.PaletteParameterDefinitions

namespace Erdos911

/-- Concrete parameters for the sparse palette construction. The very large
absolute constant is used only to keep all numerical estimates explicit. -/
theorem explicit_sparse_palette_parameters (d Δ L : ℕ) (Λ σ : ℝ)
    (hd : 1 ≤ d) (hdΔ : d ≤ Δ) (hL : 1 ≤ L) (hΛ : 1 ≤ Λ)
    (_hσ : 0 ≤ σ) (hσd : σ ≤ 128 * d)
    (hscale : Real.exp 1 * sparsePaletteConstant * paletteDensityLog Λ Δ ≤ d)
    (horder : Real.log L ≤ (d : ℝ) / 1280 *
      Real.log ((d : ℝ) / (sparsePaletteConstant * paletteDensityLog Λ Δ))) :
    Nonempty (ExplicitSparsePalette d Δ L Λ σ) := by
  let T := paletteDensityLog Λ Δ
  let D := paletteDegreeCutoff Λ Δ
  let B := sparsePaletteConstant
  let ℓ := Real.log ((d : ℝ) / (B * T))
  let p := 256 * Real.log D / d
  have hB : B = 1099511627776 := rfl
  have hBp : 0 < B := by rw [hB]; norm_num
  obtain ⟨hT, hcut, hΛD, hΔD, hlogD, hlogD1, hlogΔ⟩ :=
    palette_log_cutoff_bounds Λ Δ hΛ (hd.trans hdΔ)
  change 1 ≤ T at hT
  change 128 * Λ * Δ ≤ (D : ℝ) at hcut
  change Λ ≤ (D : ℝ) at hΛD
  change (Δ : ℝ) ≤ D at hΔD
  change Real.log D ≤ T at hlogD
  change Real.log ((D : ℝ) + 1) ≤ 2 * T at hlogD1
  change Real.log Δ ≤ T at hlogΔ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  have hTp : 0 < T := by linarith
  have hBT : 0 < B * T := mul_pos hBp hTp
  have hexp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hBd : B * T ≤ (d : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hexp hBT.le
    change Real.exp 1 * B * T ≤ (d : ℝ) at hscale
    nlinarith only [h, hscale]
  have hlarge : B ≤ (d : ℝ) := by nlinarith only [hBd, hT, hBp]
  have hDlarge : 1000 ≤ D := by
    have hdΔR : (d : ℝ) ≤ Δ := by exact_mod_cast hdΔ
    have hD : (1000 : ℝ) ≤ D := by linarith only [hlarge, hB, hdΔR, hΔD]
    exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogD0 : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hratio : Real.exp 1 ≤ (d : ℝ) / (B * T) := by
    apply (le_div_iff₀ hBT).mpr
    change Real.exp 1 * B * T ≤ (d : ℝ) at hscale
    nlinarith only [hscale]
  have hratioP : 0 < (d : ℝ) / (B * T) := div_pos hdp hBT
  have hℓ : 1 ≤ ℓ := by
    have h := Real.log_le_log (Real.exp_pos 1) hratio
    simpa only [Real.log_exp] using h
  have hp0 : 0 ≤ p := div_nonneg (mul_nonneg (by norm_num) hlogD0) hdp.le
  have hp1 : p ≤ 1 := by
    apply (div_le_one hdp).mpr
    nlinarith only [hlogD, hBd, hB, hT]
  have hmargin : 256 * σ ≤ (32768 : ℝ) * d := by linarith only [hσd]
  have hred : 256 * Real.log D ≤ p * d := by
    dsimp only [p]
    rw [div_mul_cancel₀ _ hdp.ne']
  have hexpℓ : Real.exp (-ℓ) = B * T / d := by
    dsimp only [ℓ]
    rw [Real.exp_neg, Real.exp_log hratioP, inv_div]
  have hblue : 16 * Real.exp 1 * p ≤ Real.exp (-ℓ) := by
    rw [hexpℓ]
    dsimp only [p]
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right hdp).mpr
    have he := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hlogD0
    nlinarith only [he, hlogD, hB, hT]
  have hW : (d : ℝ) ≤ (d : ℝ) * ℓ := le_mul_of_one_le_right hdp.le hℓ
  have hBW : B * T ≤ (d : ℝ) * ℓ := hBd.trans hW
  have hentropy0 := collisionPalette_log_card_le D L 32768 hL
  have hentropy1 : Real.log (Fintype.card (CollisionPalette D L 32768)) + 2 * Real.log Δ ≤
      Real.log L + 1048576 * T := by
    norm_num only [Nat.cast_ofNat] at hentropy0
    nlinarith only [hentropy0, hlogD1, hlogΔ, hT]
  have hentropy2 : 1048576 * T ≤ (d : ℝ) * ℓ / 1280 := by
    nlinarith only [hBW, hB, hT]
  have horder' : Real.log L ≤ (d : ℝ) * ℓ / 1280 := by
    change Real.log L ≤ (d : ℝ) / 1280 * ℓ at horder
    nlinarith only [horder]
  have hentropy : Real.log (Fintype.card (CollisionPalette D L 32768)) + 2 * Real.log Δ ≤
      (d : ℝ) * ℓ / 64 := by
    nlinarith only [hentropy1, hentropy2, horder', hW, hdR]
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hgeom : 128 * Real.log 2 ≤ (d : ℝ) * ℓ := by
    linarith only [hlog2, hW, hlarge, hB]
  have hlog1000 : Real.log (1000 : ℝ) ≤ 999 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1000)
    linarith only [h]
  have hcomponent : Real.log L + Real.log 1000 ≤ (d : ℝ) ^ 2 * ℓ / 512 := by
    have hd1024 : (1024 : ℝ) ≤ d := by linarith only [hlarge, hB]
    have hW0 : 0 ≤ (d : ℝ) * ℓ := by positivity
    have hprod := mul_le_mul_of_nonneg_right hd1024 hW0
    nlinarith only [hprod, horder', hlog1000, hW, hd1024]
  exact ⟨{
    D := D
    k := 32768
    p := p
    gap := ℓ
    large_cutoff := hDlarge
    large_reciprocal := by norm_num
    multiplier_le := hΛD
    probability_nonneg := hp0
    probability_le_one := hp1
    gap_nonneg := by linarith only [hℓ]
    collision_margin := by exact_mod_cast hmargin
    cutoff_bound := hcut
    red_scale := hred
    blue_base := hblue
    entropy_bound := hentropy
    geometric_bound := hgeom
    component_bound := hcomponent }⟩

end Erdos911
