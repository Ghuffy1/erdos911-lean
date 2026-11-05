import Erdos911.DenseWitnessColoring

namespace Erdos911

noncomputable def denseWitnessMultiplier (d Δ : ℕ) : ℝ :=
  (d : ℝ) / (4096 * Real.log ((Δ : ℝ) + 1))

noncomputable def denseWitnessCutoff (d Δ : ℕ) : ℕ :=
  Nat.ceil (16 * denseWitnessMultiplier d Δ * Δ)

noncomputable def denseWitnessMarkRate (d Δ : ℕ) : ℝ :=
  32 * Real.log (denseWitnessCutoff d Δ) / d

theorem log_successor_ge_half (Δ : ℕ) (hΔ : 1 ≤ Δ) :
    (1 / 2 : ℝ) ≤ Real.log ((Δ : ℝ) + 1) := by
  have htwo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at htwo
  have hΔreal : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))

theorem denseWitness_parameters (d Δ : ℕ) (hd : 4 ≤ d) (hdΔ : d ≤ Δ)
    (hlarge : 1 ≤ denseWitnessMultiplier d Δ) :
    2 ≤ denseWitnessCutoff d Δ ∧
      0 ≤ denseWitnessMarkRate d Δ ∧ denseWitnessMarkRate d Δ ≤ 1 ∧
      32 * Real.log (denseWitnessCutoff d Δ) ≤ denseWitnessMarkRate d Δ * d ∧
      2 * denseWitnessMultiplier d Δ * Δ / ((denseWitnessCutoff d Δ : ℝ) + 1) ≤ 1 / 8 ∧
      2 * denseWitnessMarkRate d Δ * denseWitnessMultiplier d Δ ≤ 1 / 16 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hΔreal : (4 : ℝ) ≤ Δ := by exact_mod_cast (hd.trans hdΔ)
  have hdΔreal : (d : ℝ) ≤ Δ := by exact_mod_cast hdΔ
  have hlog := log_successor_ge_half Δ (by omega)
  have hlogpos : 0 < Real.log ((Δ : ℝ) + 1) := by linarith
  have hmult : denseWitnessMultiplier d Δ ≤ Δ := by
    unfold denseWitnessMultiplier
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ Δ by positivity)
    nlinarith
  have hceil : 16 * denseWitnessMultiplier d Δ * Δ ≤ (denseWitnessCutoff d Δ : ℝ) :=
    Nat.le_ceil _
  have hceilUpper : (denseWitnessCutoff d Δ : ℝ) ≤ 16 * denseWitnessMultiplier d Δ * Δ + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ 16 * denseWitnessMultiplier d Δ * Δ by positivity)).le
  have hDreal : (2 : ℝ) ≤ denseWitnessCutoff d Δ := by
    have h := mul_le_mul_of_nonneg_right hlarge (show (0 : ℝ) ≤ Δ by positivity)
    nlinarith
  have hD : 2 ≤ denseWitnessCutoff d Δ := by exact_mod_cast hDreal
  have hDpos : (0 : ℝ) < denseWitnessCutoff d Δ := by linarith
  have hquad : 4 * (Δ : ℝ) + 1 ≤ ((Δ : ℝ) + 1) ^ 2 := by nlinarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ 4 * (Δ : ℝ) + 1 by positivity) hquad 2
  have hDupper : (denseWitnessCutoff d Δ : ℝ) ≤ ((Δ : ℝ) + 1) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hmult (show (0 : ℝ) ≤ Δ by positivity)
    nlinarith
  have hlogD : Real.log (denseWitnessCutoff d Δ) ≤ 4 * Real.log ((Δ : ℝ) + 1) := by
    calc
      _ ≤ Real.log (((Δ : ℝ) + 1) ^ 4) := Real.log_le_log hDpos hDupper
      _ = _ := by rw [Real.log_pow]; norm_num
  have hdegree : 4096 * Real.log ((Δ : ℝ) + 1) ≤ d := by
    have h := (le_div_iff₀ (show 0 < 4096 * Real.log ((Δ : ℝ) + 1) by positivity)).mp hlarge
    simpa only [denseWitnessMultiplier, one_mul] using h
  have hp₀ : 0 ≤ denseWitnessMarkRate d Δ := by
    unfold denseWitnessMarkRate
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) hdpos.le
  have hp₁ : denseWitnessMarkRate d Δ ≤ 1 := by
    unfold denseWitnessMarkRate
    apply (div_le_iff₀ hdpos).mpr
    nlinarith
  have hscale : 32 * Real.log (denseWitnessCutoff d Δ) = denseWitnessMarkRate d Δ * d := by
    unfold denseWitnessMarkRate
    rw [div_mul_cancel₀ _ hdpos.ne']
  have hprune : 2 * denseWitnessMultiplier d Δ * Δ /
      ((denseWitnessCutoff d Δ : ℝ) + 1) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hmarks : 2 * denseWitnessMarkRate d Δ * denseWitnessMultiplier d Δ ≤ 1 / 16 := by
    have heq : 2 * denseWitnessMarkRate d Δ * denseWitnessMultiplier d Δ =
        Real.log (denseWitnessCutoff d Δ) / (64 * Real.log ((Δ : ℝ) + 1)) := by
      unfold denseWitnessMarkRate denseWitnessMultiplier
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  exact ⟨hD, hp₀, hp₁, hscale.le, hprune, hmarks⟩

theorem denseWitness_host_budget (d Δ : ℕ) (hd : 4 ≤ d) (hdΔ : d ≤ Δ)
    (hlarge : 1 ≤ denseWitnessMultiplier d Δ) (e m : ℝ) (he : 0 < e)
    (hm : m ≤ denseWitnessMultiplier d Δ * e) :
    2 * m * Δ / ((denseWitnessCutoff d Δ : ℝ) + 1) + 2 * denseWitnessMarkRate d Δ * m < e := by
  obtain ⟨hD, hp, _, _, hprune, hmarks⟩ := denseWitness_parameters d Δ hd hdΔ hlarge
  have hden : 0 < (denseWitnessCutoff d Δ : ℝ) + 1 := by positivity
  have hpruneM : 2 * m * Δ / ((denseWitnessCutoff d Δ : ℝ) + 1) ≤ e / 8 := by
    calc
      _ = m * (2 * Δ / ((denseWitnessCutoff d Δ : ℝ) + 1)) := by ring
      _ ≤ (denseWitnessMultiplier d Δ * e) * (2 * Δ / ((denseWitnessCutoff d Δ : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ = (2 * denseWitnessMultiplier d Δ * Δ / ((denseWitnessCutoff d Δ : ℝ) + 1)) * e := by ring
      _ ≤ (1 / 8 : ℝ) * e := mul_le_mul_of_nonneg_right hprune he.le
      _ = e / 8 := by ring
  have hmarksM : 2 * denseWitnessMarkRate d Δ * m ≤ e / 16 := by
    calc
      _ ≤ 2 * denseWitnessMarkRate d Δ * (denseWitnessMultiplier d Δ * e) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = (2 * denseWitnessMarkRate d Δ * denseWitnessMultiplier d Δ) * e := by ring
      _ ≤ (1 / 16 : ℝ) * e := mul_le_mul_of_nonneg_right hmarks he.le
      _ = e / 16 := by ring
  linarith

end Erdos911
