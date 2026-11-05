import Erdos911.BoundedComponentPalette

namespace Erdos911

noncomputable def polynomialCoreCoefficient (B A : ℕ) : ℝ :=
  3 * boundedPaletteConstant * (2 * B + 131) + 8192 * A + 1

theorem polynomialCoreCoefficient_pos (B A : ℕ) : 1 ≤ polynomialCoreCoefficient B A := by
  unfold polynomialCoreCoefficient boundedPaletteConstant
  nlinarith only [Nat.cast_nonneg (α := ℝ) B, Nat.cast_nonneg (α := ℝ) A]

theorem polynomial_palette_density_log (B d : ℕ) (hd : 3 ≤ d) :
    paletteDensityLog ((d : ℝ) ^ (B + 3)) (d ^ B) ≤ (2 * (B : ℝ) + 131) * Real.log d := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlogd : 1 ≤ Real.log d := by
    have he : Real.exp 1 ≤ (d : ℝ) := Real.exp_one_lt_three.le.trans (by exact_mod_cast hd)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hlog128 : Real.log (128 : ℝ) ≤ 127 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 128)
    linarith only [h]
  unfold paletteDensityLog
  rw [Nat.cast_pow, Real.log_mul (by positivity) (pow_pos hdp _).ne',
    Real.log_mul (by norm_num) (pow_pos hdp _).ne', Real.log_pow, Real.log_pow]
  push_cast
  nlinarith only [hlogd, hlog128]

/-- Components of polynomial order and logarithmic minimum degree
already force a polynomial size-Ramsey multiplier. -/
theorem polynomial_component_palette_ramsey (B A d s : ℕ) (hd : 3 ≤ d)
    (hs : polynomialCoreCoefficient B A * Real.log d ≤ (s : ℝ)) (hsΔ : s ≤ d ^ B)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 0 < Fintype.card V) (hmin : ∀ v, s ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ d ^ B)
    (horder : ∀ t : G.ConnectedComponent, Nat.card t.supp ≤ d ^ A) :
    (d : ℝ) ^ (B + 3) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hlogd : 1 ≤ Real.log d := by
    have he : Real.exp 1 ≤ (d : ℝ) := Real.exp_one_lt_three.le.trans (by exact_mod_cast hd)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hC := polynomialCoreCoefficient_pos B A
  have hsR : (1 : ℝ) ≤ s := by nlinarith only [hs, hC, hlogd]
  have hsN : 1 ≤ s := by exact_mod_cast hsR
  have hΛ : 1 ≤ (d : ℝ) ^ (B + 3) := one_le_pow₀ hdR
  have hL : 1 ≤ d ^ A := Nat.one_le_pow _ _ (by omega)
  have hB : 0 < boundedPaletteConstant := by norm_num [boundedPaletteConstant]
  have hT := (palette_log_cutoff_bounds ((d : ℝ) ^ (B + 3)) (d ^ B) hΛ
    (Nat.one_le_pow _ _ (by omega))).1
  have hTup := polynomial_palette_density_log B d hd
  have hscale : Real.exp 1 * boundedPaletteConstant *
      paletteDensityLog ((d : ℝ) ^ (B + 3)) (d ^ B) ≤ (s : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
      (show 0 ≤ boundedPaletteConstant * paletteDensityLog ((d : ℝ) ^ (B + 3)) (d ^ B) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hTup (show 0 ≤ 3 * boundedPaletteConstant by positivity)
    have h₃ : 3 * boundedPaletteConstant * (2 * (B : ℝ) + 131) ≤ polynomialCoreCoefficient B A := by
      dsimp only [polynomialCoreCoefficient, boundedPaletteConstant]
      nlinarith only [Nat.cast_nonneg (α := ℝ) A]
    have h₄ := mul_le_mul_of_nonneg_right h₃ (by linarith only [hlogd] : 0 ≤ Real.log d)
    nlinarith only [h₁, h₂, h₄, hs]
  have hlogratio := (bounded_palette_scale_large s (d ^ B) ((d : ℝ) ^ (B + 3)) hΛ
    (Nat.one_le_pow _ _ (by omega)) hscale).2
  have horderbound : Real.log (d ^ A : ℕ) ≤ (s : ℝ) / 8192 := by
    rw [Nat.cast_pow, Real.log_pow]
    have hC' : 8192 * (A : ℝ) ≤ polynomialCoreCoefficient B A := by
      dsimp only [polynomialCoreCoefficient, boundedPaletteConstant]
      nlinarith only [Nat.cast_nonneg (α := ℝ) B]
    have hm := mul_le_mul_of_nonneg_right hC' (by linarith only [hlogd] : 0 ≤ Real.log d)
    nlinarith only [hm, hs]
  apply bounded_component_palette_ramsey s (d ^ B) (d ^ A) ((d : ℝ) ^ (B + 3)) G
    hV hsN hsΔ hL hΛ hmin hmax horder hscale
  exact horderbound.trans (le_mul_of_one_le_right (by positivity) hlogratio)

end Erdos911
