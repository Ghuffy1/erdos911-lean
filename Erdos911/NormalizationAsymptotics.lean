import Erdos911.IncidenceGraph
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace Erdos911

theorem normalization_failure_tends_to_zero (c K : ℝ) (B : ℕ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp 1 * Real.exp (-c * x / 8) * (K * x ^ B + 1))
      atTop (nhds 0) := by
  have hp : Tendsto (fun x : ℝ => x ^ B * Real.exp (-(c / 8) * x)) atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (B : ℝ) (c / 8) (by positivity)
  have he : Tendsto (fun x : ℝ => Real.exp (-(c / 8) * x)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (c / 8) (by positivity)
  have hs : Tendsto
      (fun x : ℝ => (Real.exp 1 * K) * (x ^ B * Real.exp (-(c / 8) * x)) +
        Real.exp 1 * Real.exp (-(c / 8) * x)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hp.const_mul (Real.exp 1 * K)).add (he.const_mul (Real.exp 1))
  convert hs using 1
  funext x
  rw [show -c * x / 8 = -(c / 8) * x by ring]
  ring

theorem eventually_normalization_condition (c K : ℝ) (B : ℕ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp 1 * Real.exp (-c * x / 8) * (K * x ^ B + 1) ≤ 1 := by
  have h := (normalization_failure_tends_to_zero c K B hc).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  exact h.mono (fun _ hx => hx.le)

/-- A polynomial number of coordinate dependencies is dominated by the
exponential lower-tail estimate when the mean is at least linear in d. -/
theorem degree_normalization_eventually {c K : ℝ} (B : ℕ) (hc : 0 < c) :
    ∃ d₀ : ℝ, ∀ d ≥ d₀, ∀ q a b r : ℕ,
      c * d ≤ (q : ℝ) / b * r →
      (a * b : ℝ) ≤ K * d ^ B →
      Real.exp 1 * Real.exp (-((q : ℝ) / b * r) / 8) * ((a * b : ℕ) + 1) ≤ 1 := by
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp (eventually_normalization_condition c K B hc)
  refine ⟨d₀, ?_⟩
  intro d hd q a b r hmean hdegree
  have he : Real.exp (-((q : ℝ) / b * r) / 8) ≤ Real.exp (-c * d / 8) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hdegree' : (((a * b : ℕ) + 1 : ℝ)) ≤ K * d ^ B + 1 := by
    push_cast
    linarith
  calc
    Real.exp 1 * Real.exp (-((q : ℝ) / b * r) / 8) * ((a * b : ℕ) + 1) ≤
        Real.exp 1 * Real.exp (-c * d / 8) * (K * d ^ B + 1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left he (Real.exp_pos 1).le
      · exact hdegree'
      · positivity
      · positivity
    _ ≤ 1 := hd₀ d hd

end Erdos911
