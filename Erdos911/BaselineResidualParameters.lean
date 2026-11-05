import Erdos911.ResidualLogBudget

open Filter

namespace Erdos911

theorem eventually_baseline_residual_bounds (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 4 ≤ d ∧ 2 ≤ Real.log d ∧ 1 ≤ Real.log (Real.log d) ∧
      baselineSampleRate A d ≤ 1 / 5 ∧ baselineResidualRate d ≤ 1 ∧
      baselineResidualError A d ≤ 1 ∧ 2 ≤ baselineBlockSize d ∧
      (baselineBlockSize d : ℝ) ≤ (d : ℝ) / 4 := by
  have hsample := (baselineSampleRate_tends_to_zero A).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 5 by norm_num))
  have hresidual := baselineResidualRate_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have herror := (baselineResidualError_tends_to_zero A).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hblock := baselineBlockSize_ratio_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  have hloglog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (hlog.and (hloglog.and (hsample.and (hresidual.and (herror.and hblock)))))
  refine ⟨max 4 (Nat.ceil x₀), ?_⟩
  intro d hd
  have hd4 : 4 ≤ d := (le_max_left 4 (Nat.ceil x₀)).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by
    exact_mod_cast (le_max_right 4 (Nat.ceil x₀)).trans hd)
  obtain ⟨hl, hll, hs, hr, he, hq⟩ := hx₀ d hx
  have hpow : (1 : ℝ) < (Real.log d) ^ 4 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hl 4
    norm_num at h
    linarith
  have hq2 : 2 ≤ baselineBlockSize d := by
    change 1 + 1 ≤ Nat.ceil ((Real.log d) ^ 4)
    apply Nat.add_one_le_ceil_iff.mpr
    simpa only [Nat.cast_one] using hpow
  have hqsmall : (baselineBlockSize d : ℝ) ≤ (d : ℝ) / 4 := by
    have h := (div_lt_iff₀ hdpos).mp hq
    linarith
  exact ⟨hd4, hl, hll, hs.le, hr.le, he.le, hq2, hqsmall⟩

/-- The sampling size and logarithmic local-lemma budget hold for every
component order and every polynomially bounded host degree beyond one
degree threshold. -/
theorem baseline_residual_parameters_uniform (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D : ℕ, d ≤ D → D ≤ d ^ A →
      ∀ k : ℕ, d ≤ k → ∀ b : ℕ, (d : ℝ) * k / 8 ≤ b →
      4 ≤ d ∧ 2 ≤ baselineBlockSize d ∧ 2 * baselineBlockSize d ≤ d ∧
      (1 / 4 : ℝ) * d + baselineBlockSize d < (11 / 16 : ℝ) * d ∧
      0 < baselineSampleRate A d ∧ baselineSampleRate A d ≤ 1 ∧
      0 < baselineResidualRate d ∧ baselineResidualRate d ≤ 1 ∧
      baselineSeedOrder A d k ≤ k ∧
      3 * k * (baselineSampleRate A d + (4 * (D * D : ℕ) + 1 : ℝ) *
        Real.exp (-((1 / 16 : ℝ) ^ 2 * (baselineSampleRate A d * d)) / 128)) ≤
        (baselineSeedOrder A d k : ℝ) ∧
      Real.log (8 * seedAssignmentCountBound k D D (baselineSeedOrder A d k)
        (baselineBlockSize d) / baselineResidualRate d) ≤ baselineResidualRate d * b / 2 := by
  obtain ⟨d₀, hd₀⟩ := eventually_baseline_residual_bounds A
  refine ⟨d₀, ?_⟩
  intro d hd D hD hDpow k hk b hb
  obtain ⟨hd4, hlog, hloglog, hsample, hresidual, herror, hq2, hqsmall⟩ := hd₀ d hd
  have hdpos : 0 < d := by omega
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hqnat : 2 * baselineBlockSize d ≤ d := by
    exact_mod_cast (show (2 : ℝ) * baselineBlockSize d ≤ d by linarith)
  have hgap : (1 / 4 : ℝ) * d + baselineBlockSize d < (11 / 16 : ℝ) * d := by
    linarith
  have hp : 0 < baselineResidualRate d := by
    unfold baselineResidualRate
    positivity
  obtain ⟨_, _, hs⟩ := baselineSeedOrder_bounds A d k hdpos (by linarith) hk hsample
  refine ⟨hd4, hq2, hqnat, hgap, baselineSampleRate_pos A d hdpos (by linarith),
    by linarith, hp, hresidual, hs, ?_, ?_⟩
  · exact baseline_seed_sampling_bound A d D k hdpos (by linarith) hD hDpow
  · exact baseline_residual_log_budget A d D k b (by omega) (by linarith)
      hloglog hk hD hDpow hsample herror hb

end Erdos911
