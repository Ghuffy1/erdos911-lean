import Erdos911.UniformEntropyThreshold

open Filter

namespace Erdos911

noncomputable def polynomialEntropyError (A B : ℕ) (x : ℝ) : ℝ :=
  ((4 * A + 2 * B + 5 : ℝ) * Real.log x + 6) / x

theorem polynomialEntropyError_tends_to_zero (A B : ℕ) :
    Tendsto (polynomialEntropyError A B) atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h := (hlog.const_mul (4 * A + 2 * B + 5 : ℝ)).add (hinv.const_mul 6)
  convert h using 1
  · funext x
    unfold polynomialEntropyError
    ring_nf
  · ring_nf

theorem biased_probability_tends_to_zero (K : ℝ) :
    Tendsto (fun x : ℝ => K * Real.log x / x) atTop (nhds 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa only [mul_zero, mul_div_assoc] using h.const_mul K

theorem polynomial_entropy_threshold_bound (A B d : ℕ) (K : ℝ)
    (hd : 0 < d) (hlog : 1 ≤ Real.log d) (hK : 1 ≤ K) :
    Real.log d - Real.log (Real.log d) - Real.log K - polynomialEntropyError A B d ≤
      biasedEntropyThreshold d (d ^ B) (d ^ A) (K * Real.log d / d) (1 / d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hKpos : 0 < K := by linarith
  have hlogpos : 0 < Real.log d := by linarith
  have hlogp : Real.log (K * Real.log d / d) =
      Real.log K + Real.log (Real.log d) - Real.log d := by
    rw [Real.log_div (mul_pos hKpos hlogpos).ne' hdpos.ne',
      Real.log_mul hKpos.ne' hlogpos.ne']
  have hlogΛ : Real.log ((d : ℝ) ^ A * d) =
      (A + 1 : ℝ) * Real.log d := by
    rw [Real.log_mul (pow_pos hdpos _).ne' hdpos.ne', Real.log_pow]
    ring
  have hlogΔ : Real.log (((d ^ B : ℕ) : ℝ)) = B * Real.log d := by
    rw [Nat.cast_pow, Real.log_pow]
  have hidentity : biasedEntropyThreshold d (d ^ B) (d ^ A) (K * Real.log d / d) (1 / d) =
      Real.log d - Real.log (Real.log d) - Real.log K - polynomialEntropyError A B d +
        (Real.log (Real.log d) + Real.log K) / d + 2 / (d : ℝ) ^ 2 := by
    unfold biasedEntropyThreshold polynomialEntropyError
    rw [hlogp, hlogΛ, hlogΔ]
    field_simp
    ring
  rw [hidentity]
  have hloglog : 0 ≤ Real.log (Real.log d) := Real.log_nonneg hlog
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hcorrection : 0 ≤ (Real.log (Real.log d) + Real.log K) / d + 2 / (d : ℝ) ^ 2 :=
    add_nonneg (div_nonneg (add_nonneg hloglog hlogK) hdpos.le) (by positivity)
  linarith

theorem eventually_polynomial_entropy_parameters (A B : ℕ) (K : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 4 ≤ d ∧ 1 ≤ Real.log d ∧
      K * Real.log d / d ≤ 1 / 2 ∧ polynomialEntropyError A B d ≤ 1 / 2 := by
  have hp := (biased_probability_tends_to_zero K).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have he := (polynomialEntropyError_tends_to_zero A B).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hl.and (hp.and he))
  refine ⟨max 4 (Nat.ceil x₀), ?_⟩
  intro d hd
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by
    exact_mod_cast (le_max_right 4 (Nat.ceil x₀)).trans hd)
  have h := hx₀ d hx
  exact ⟨(le_max_left 4 (Nat.ceil x₀)).trans hd, h.1, h.2.1.le, h.2.2.le⟩

end Erdos911
