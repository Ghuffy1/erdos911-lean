import Erdos911.BaselineResidualParameters

open Filter

namespace Erdos911

noncomputable def baselineBlockRate (A : ℕ) (x : ℝ) : ℝ :=
  32768 * ((A : ℝ) + 1) * Real.log x / x

theorem baselineBlockRate_tends_to_zero (A : ℕ) :
    Tendsto (baselineBlockRate A) atTop (nhds 0) :=
  biased_probability_tends_to_zero (32768 * ((A : ℝ) + 1))

theorem baselineBlockRate_nonneg (A d : ℕ) (hlog : 1 ≤ Real.log d) :
    0 ≤ baselineBlockRate A d := by
  unfold baselineBlockRate
  positivity

theorem baseline_block_thresholds (d k a : ℕ) (hd : 2048 ≤ d) (hk : d ≤ k)
    (haverage : d * k ≤ 2 * a) :
    4 ≤ d / 512 ∧ d / 512 ≤ k ∧ (d / 512) * k ≤ 2 * (a / 256) ∧
      a / 2 + 17 * (a / 256 + 3 * (a / 1024)) ≤ a ∧
      (d : ℝ) * k / 8 ≤ (a / 2 : ℕ) := by
  have hdk : d ≤ d * k := by
    calc
      d = d * 1 := by omega
      _ ≤ d * k := Nat.mul_le_mul_left d (by omega)
  have ha : 2 ≤ a := by omega
  have hdiv := Nat.div_mul_le_self d 512
  have hscaled := Nat.mul_le_mul_right k hdiv
  have hblock : (d / 512) * k ≤ a / 256 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    nlinarith only [hscaled, haverage]
  refine ⟨by omega, (Nat.div_le_self d 512).trans hk, by omega, by omega, ?_⟩
  have hnat : d * k ≤ 8 * (a / 2) := by omega
  have hreal : (d : ℝ) * k ≤ 8 * (a / 2 : ℕ) := by exact_mod_cast hnat
  linarith

theorem baseline_block_scale (A d D : ℕ) (hd : 2048 ≤ d)
    (hlog : 1 ≤ Real.log d) (hD : 1 ≤ D) (hDpow : D ≤ d ^ A) :
    32 * Real.log D ≤ baselineBlockRate A d * (d / 512 : ℕ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogD : Real.log D ≤ (A : ℝ) * Real.log d := by
    calc
      Real.log D ≤ Real.log ((d : ℝ) ^ A) := Real.log_le_log hDpos (by exact_mod_cast hDpow)
      _ = _ := Real.log_pow ..
  have hfloor : d ≤ 1024 * (d / 512) := by omega
  have hfloorR : (d : ℝ) ≤ 1024 * (d / 512 : ℕ) := by exact_mod_cast hfloor
  have hscaled := mul_le_mul_of_nonneg_left hfloorR (baselineBlockRate_nonneg A d hlog)
  have heq : baselineBlockRate A d * d = 32768 * ((A : ℝ) + 1) * Real.log d := by
    unfold baselineBlockRate
    exact div_mul_cancel₀ _ hdpos.ne'
  rw [heq] at hscaled
  nlinarith

/-- One threshold provides every numerical hypothesis used by the block
and residual marking constructions, uniformly over component order. -/
theorem baseline_coloring_parameters_uniform (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D : ℕ, d ≤ D → D ≤ d ^ A →
      ∀ k a : ℕ, d ≤ k → d * k ≤ 2 * a →
      0 < d ∧ 2 ≤ D ∧ 4 ≤ d / 512 ∧ d / 512 ≤ k ∧
      baselineBlockSize d ≤ D ∧ (d / 512) * k ≤ 2 * (a / 256) ∧
      0 ≤ baselineBlockRate A d ∧ baselineBlockRate A d ≤ 1 ∧
      32 * Real.log D ≤ baselineBlockRate A d * (d / 512 : ℕ) ∧
      2 ≤ baselineBlockSize d ∧ 2 * baselineBlockSize d ≤ d ∧
      (1 / 4 : ℝ) * d + baselineBlockSize d < (11 / 16 : ℝ) * d ∧
      0 < baselineSampleRate A d ∧ baselineSampleRate A d ≤ 1 ∧
      0 < baselineResidualRate d ∧ baselineResidualRate d ≤ 1 ∧
      3 * k * (baselineSampleRate A d + (4 * (D * D : ℕ) + 1 : ℝ) *
        Real.exp (-((1 / 16 : ℝ) ^ 2 * (baselineSampleRate A d * d)) / 128)) ≤
        (baselineSeedOrder A d k : ℝ) ∧
      a / 2 + 17 * (a / 256 + 3 * (a / 1024)) ≤ a ∧
      Real.log (8 * seedAssignmentCountBound k D D (baselineSeedOrder A d k)
        (baselineBlockSize d) / baselineResidualRate d) ≤ baselineResidualRate d * (a / 2 : ℕ) / 2 := by
  obtain ⟨d₁, hd₁⟩ := baseline_residual_parameters_uniform A
  obtain ⟨d₂, hd₂⟩ := eventually_baseline_residual_bounds A
  have hp := (baselineBlockRate_tends_to_zero A).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hp
  refine ⟨max 2048 (max d₁ (max d₂ (Nat.ceil x₀))), ?_⟩
  intro d hd D hD hDpow k a hk haverage
  have hd2048 : 2048 ≤ d := (le_max_left _ _).trans hd
  have hdrest : max d₁ (max d₂ (Nat.ceil x₀)) ≤ d := (le_max_right _ _).trans hd
  have hd₁' : d₁ ≤ d := (le_max_left _ _).trans hdrest
  have hd₂' : d₂ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hdrest)
  have hceil : Nat.ceil x₀ ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hdrest)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hceil)
  have hlog : 1 ≤ Real.log d := by linarith [(hd₂ d hd₂').2.1]
  obtain ⟨hdBlock, horder, havgBlock, hretention, hmass⟩ :=
    baseline_block_thresholds d k a hd2048 hk haverage
  obtain ⟨_, hq, hsmall, hgap, hα₀, hα₁, hp₀, hp₁, _, hseed, hbudget⟩ :=
    hd₁ d hd₁' D hD hDpow k hk (a / 2) hmass
  exact ⟨by omega, by omega, hdBlock, horder, by omega, havgBlock,
    baselineBlockRate_nonneg A d hlog, (hx₀ d hx).le,
    baseline_block_scale A d D hd2048 hlog (by omega) hDpow,
    hq, hsmall, hgap, hα₀, hα₁, hp₀, hp₁, hseed, hretention, hbudget⟩

end Erdos911
