import Erdos911.BandLogParameters
import Erdos911.NormalizationAsymptotics

open Filter

namespace Erdos911

/-- One threshold discharges all rounding, degree-ratio, and
normalization estimates, uniformly over the global degree bound a. -/
theorem band_parameters_uniform (B : ℕ) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀,
      131072 ≤ q ∧ 1 ≤ bandDegree q ∧ 1 ≤ Real.log q ∧
      1 ≤ Real.log (bandDegree q) ∧ q ≤ 131072 * bandDegree q ∧
      bandLeftThreshold q + 2 * q ≤
        524288 * bandDegree q * (Real.log (bandDegree q)) ^ nearRegularDegreePower ∧
      (bandDegree q : ℝ) * (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) ≤
        (bandDegree q : ℝ) / (2 * q) * bandLeftFloor q / 2 ∧
      ∀ a : ℕ, a ≤ (2 * q) ^ B → a ≤ bandDegree q ^ (B + 1) ∧
        Real.exp 1 * Real.exp (-((bandDegree q : ℝ) / (2 * q : ℕ) * bandLeftFloor q) / 8) *
          ((a * (2 * q) : ℕ) + 1) ≤ 1 := by
  have hpower := ((tendsto_rpow_atTop
    (show (0 : ℝ) < nearRegularDegreePower / 2 by norm_num [nearRegularDegreePower])).comp
      Real.tendsto_log_atTop).eventually (eventually_ge_atTop (64 : ℝ))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  obtain ⟨xlog, hxlog⟩ := eventually_atTop.mp (hpower.and hlog)
  obtain ⟨xnorm, hxnorm⟩ := degree_normalization_eventually
    (c := 1 / 4194304) (K := (2 : ℝ) ^ (B + 1)) (B + 1) (by norm_num)
  let N := max 131072 (max (262144 ^ B) (Nat.ceil (Real.exp 1)))
  refine ⟨max (65536 * N) (max 131072 (Nat.ceil (max xlog xnorm))), ?_⟩
  intro q hq
  have hqlarge : 131072 ≤ q := by omega
  have hN : N ≤ bandDegree q := by
    unfold bandDegree
    omega
  have hdl : 131072 ≤ bandDegree q := (le_max_left _ _).trans hN
  have hdpow : 262144 ^ B ≤ bandDegree q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hdexp : Real.exp 1 ≤ (bandDegree q : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (show Nat.ceil (Real.exp 1) ≤ bandDegree q by
      exact (le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hlogd : 1 ≤ Real.log (bandDegree q) := by
    have h := Real.log_le_log (Real.exp_pos 1) hdexp
    simpa only [Real.log_exp] using h
  have hx : max xlog xnorm ≤ (q : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show Nat.ceil (max xlog xnorm) ≤ q by omega))
  obtain ⟨hp, hl⟩ := hxlog q ((le_max_left _ _).trans hx)
  obtain ⟨hdpos, _, hqbound, _⟩ := bandDegree_bounds q hqlarge
  refine ⟨hqlarge, hdpos, hl, hlogd, hqbound,
    band_low_degree_bound q hqlarge hdl hlogd, band_high_degree_bound q hqlarge hl hp, ?_⟩
  intro a ha
  refine ⟨band_polynomial_degree_bound B q a hqbound hdpow ha, ?_⟩
  have hmean : (1 / 4194304 : ℝ) * q ≤
      (bandDegree q : ℝ) / (2 * q : ℕ) * bandLeftFloor q := by
    have h := band_normalization_mean_lower q hqlarge hl
    simpa only [Nat.cast_mul, Nat.cast_ofNat, one_div, div_eq_mul_inv, mul_comm, one_mul] using h
  have hdep : (a * (2 * q) : ℝ) ≤ (2 : ℝ) ^ (B + 1) * (q : ℝ) ^ (B + 1) := by
    have h := Nat.mul_le_mul_right (2 * q) ha
    have h' : a * (2 * q) ≤ (2 * q) ^ (B + 1) := by simpa only [pow_succ] using h
    exact_mod_cast (show a * (2 * q) ≤ 2 ^ (B + 1) * q ^ (B + 1) by
      simpa only [Nat.mul_pow] using h')
  exact hxnorm q ((le_max_right _ _).trans hx) (bandDegree q) a (2 * q) (bandLeftFloor q) hmean
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdep)

end Erdos911
