import Erdos911.SeedEventLogBounds
import Erdos911.ExponentialEventLogParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace Erdos911

noncomputable def seedEventExponent (d k : ℕ) : ℝ :=
  (k : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ)

theorem seedEventExponent_ge_one (d k : ℕ) (hd : 1 ≤ d) (hdk : d ≤ k) :
    1 ≤ seedEventExponent d k := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hp : (d : ℝ) ^ (3 / 4 : ℝ) ≤ d := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ d by exact_mod_cast hd) (show (3 / 4 : ℝ) ≤ 1 by norm_num)
  exact (one_le_div (Real.rpow_pos_of_pos hdR _)).mpr (hp.trans (by exact_mod_cast hdk))

/-- A cubic logarithmic seed count is negligible relative to the
sublinear-in-d loss in the robust matching exponent. -/
theorem seed_event_log_budget_uniform (A h t : ℕ) (C : ℝ) (hC : 0 ≤ C) (hh : 1 ≤ h) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k D s q₁ q₂ : ℕ,
      d ≤ k → 1 ≤ D → D ≤ d ^ A → s ≤ k →
      (s : ℝ) ≤ C * k * (Real.log d) ^ 2 / d →
      1 ≤ q₁ → 1 ≤ q₂ → q₁ ≤ d → q₂ ≤ d →
      1 ≤ seedEventExponent d k ∧
      Real.log (8 * (seedEventCountBound k D s q₂ : ℝ) * seedEventSupportBound k D q₁ t h) ≤
        seedEventExponent d k / 2 := by
  have hlimit : Tendsto (fun x : ℝ =>
      seedEventLogCoefficient A h t C * (Real.log x) ^ 3 / x ^ (1 / 4 : ℝ)) atTop (nhds 0) := by
    have hp := (isLittleO_log_rpow_rpow_atTop (3 : ℕ)
      (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, mul_zero, mul_div_assoc] using
      hp.const_mul (seedEventLogCoefficient A h t C)
  have hsmall := hlimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hsmall.and hlogs)
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd k D s q₁ q₂ hdk hD hDpow hs hseed hq₁ hq₂ hq₁d hq₂d
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hxd : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by
    exact_mod_cast (le_max_right 1 (Nat.ceil x₀)).trans hd)
  obtain ⟨hscale, hlog⟩ := hx₀ d hxd
  have hquarter : (0 : ℝ) < (d : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hdR _
  have hthreequarters : (0 : ℝ) < (d : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hdR _
  have hpower : (d : ℝ) ^ (1 / 4 : ℝ) * (d : ℝ) ^ (3 / 4 : ℝ) = d := by
    rw [← Real.rpow_add hdR]
    norm_num
  have hnumerator : seedEventLogCoefficient A h t C * (Real.log d) ^ 3 ≤
      (d : ℝ) ^ (1 / 4 : ℝ) / 2 := by
    have hx := (div_lt_iff₀ hquarter).mp hscale
    linarith
  have hcomparison : (k : ℝ) / d * (seedEventLogCoefficient A h t C * (Real.log d) ^ 3) ≤
      seedEventExponent d k / 2 := by
    calc
      _ ≤ (k : ℝ) / d * ((d : ℝ) ^ (1 / 4 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hnumerator (by positivity)
      _ = seedEventExponent d k / 2 := by
        unfold seedEventExponent
        field_simp
        nlinarith only [congrArg (fun x : ℝ => (k : ℝ) * x) hpower]
  exact ⟨seedEventExponent_ge_one d k hd1 hdk,
    (uniform_seed_event_log_bound A d k D s q₁ q₂ t h C hd1 hdk hD hDpow hs hC hlog hseed
      hq₁ hq₂ hq₁d hq₂d hh).trans hcomparison⟩

theorem seed_event_parameters_uniform (A h t : ℕ) (C : ℝ) (hC : 0 ≤ C) (hh : 1 ≤ h) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k D s q₁ q₂ : ℕ,
      d ≤ k → 1 ≤ D → D ≤ d ^ A → s ≤ k →
      (s : ℝ) ≤ C * k * (Real.log d) ^ 2 / d →
      1 ≤ q₁ → 1 ≤ q₂ → q₁ ≤ d → q₂ ≤ d →
      ∀ a : ℝ, seedEventExponent d k ≤ a → ∃ ν : ℝ,
      0 ≤ ν ∧ Real.exp (-a / 2) ≤ 1 / 2 ∧
      (seedEventCountBound k D s q₂ : ℝ) * Real.exp (-a / 2) ≤ ν ∧
      4 * ν * seedEventSupportBound k D q₁ t h ≤ a ∧ Real.exp (2 * ν) ≤ 2 := by
  obtain ⟨d₀, hd₀⟩ := seed_event_log_budget_uniform A h t C hC hh
  refine ⟨max 1 d₀, ?_⟩
  intro d hd k D s q₁ q₂ hdk hD hDpow hs hseed hq₁ hq₂ hq₁d hq₂d a ha
  obtain ⟨hexponent, hlog⟩ := hd₀ d ((le_max_right _ _).trans hd) k D s q₁ q₂
    hdk hD hDpow hs hseed hq₁ hq₂ hq₁d hq₂d
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hN := seedEventCountBound_pos k D s q₂ (by omega) (by omega) (by omega)
  have hb := seedEventSupportBound_pos k D q₁ t h (by omega) (by omega) (by omega) (by omega)
  exact ⟨1 / (8 * (seedEventSupportBound k D q₁ t h : ℝ)),
    exponential_event_log_parameters _ _ hN hb a (hexponent.trans ha) (hlog.trans (by linarith))⟩

end Erdos911
