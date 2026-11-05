import Erdos911.NearRegularTypeRatios
import Erdos911.TripleLogEntropy

open Filter Asymptotics

namespace Erdos911

theorem nearRegularTypeError_tends_to_zero :
    Tendsto nearRegularTypeError atTop (nhds 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (2 : ℕ)
    (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero).const_mul 64
  change Tendsto (fun x : ℝ => 64 * (Real.log x) ^ 2 / x) atTop (nhds 0)
  simpa only [Real.rpow_natCast, Real.rpow_one,
    mul_div_assoc, mul_zero] using h

theorem near_regular_entropy_margin_uniform (A M : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      1 ≤ Real.log d ∧ 0 < Real.log (Real.log d) ∧
      Real.log (Real.log (Real.log d)) + Real.log (64 * M * A) +
        Real.log 256 + 7 + 3 * Real.log 2 + nearRegularTypeError d ≤
          7 * nearRegularDegreePower * Real.log (Real.log d) := by
  let C := Real.log (64 * M * A) + Real.log 256 + 7 + 3 * Real.log 2
  have hmain := (component_entropy_error_tends_to_zero C).comp Real.tendsto_log_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.log (Real.log x))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have herror := nearRegularTypeError_tends_to_zero.mul hinv
  have hsum : Tendsto (fun x : ℝ =>
      (Real.log (Real.log (Real.log x)) + C + nearRegularTypeError x) /
        Real.log (Real.log x)) atTop (nhds 0) := by
    have h := hmain.add herror
    simp only [add_zero, mul_zero] at h
    convert h using 1
    funext x
    simp only [Function.comp_def]
    ring
  have hsmall := hsum.eventually (eventually_lt_nhds
    (show (0 : ℝ) < 7 * nearRegularDegreePower by norm_num [nearRegularDegreePower]))
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hsmall.and hlogs)
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd
  obtain ⟨hsmall, hlog⟩ := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast hd))
  have hloglog : 0 < Real.log (Real.log d) := Real.log_pos (by linarith)
  refine ⟨by linarith, hloglog, ?_⟩
  have h := (div_lt_iff₀ hloglog).mp hsmall
  dsimp only [C] at h
  linarith

theorem near_regular_star_level_eq (d D : ℝ) (a : ℕ) (hD : 0 < D)
    (hlog : 0 < Real.log d) :
    (a : ℝ) / 32 * Real.log (D / nearRegularCommonCutoff D d) =
      8 * nearRegularDegreePower * a * Real.log (Real.log d) := by
  have hp := Real.rpow_pos_of_pos hlog nearRegularLossPower
  have hratio : D / nearRegularCommonCutoff D d = (Real.log d) ^ nearRegularLossPower := by
    unfold nearRegularCommonCutoff
    field_simp
  rw [hratio, Real.log_rpow hlog]
  norm_num [nearRegularLossPower, nearRegularDegreePower]
  ring

/-- Both bad-type exponents have a full component-edge-count gap below
the triple-log class threshold, uniformly in the component order. -/
theorem near_regular_type_gaps (A M : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k a D Δ j : ℕ,
      d ≤ k → 0 < a → 0 < D → D ≤ d ^ 3 →
      (d : ℝ) * k ≤ 2 * a → 2 * (a : ℝ) ≤ (Δ : ℝ) * k →
      (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
      16 * M * d * Δ ≤ (D : ℝ) → (D : ℝ) ≤ 32 * M * d * Δ →
      nearRegularLossFraction 1024 d * a / 32 ≤ (j : ℝ) →
      starBadTypeLogBound (tolerantTupleOrder d) k a D D
          ((a : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d)) ≤
        (a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2) - a ∧
      repeatedTypeExponent k a j D (D * k)
          (nearRegularBlockSize d * nearRegularBlockSize d) ≤
        (a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2) - a := by
  obtain ⟨d₁, hd₁⟩ := near_regular_entropy_margin_uniform A M
  refine ⟨max 1 d₁, ?_⟩
  intro d hd k a D Δ j hk ha hD hDpow haverage hupper hdegree hlower hhost hj
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  obtain ⟨hlog, hloglog, hmargin⟩ := hd₁ d ((le_max_right _ _).trans hd)
  have hlogpos : 0 < Real.log d := by linarith
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have havailable := near_regular_available_log_upper A M d k a D Δ hA hM hd1 hk ha hD
    hlogpos haverage hdegree hhost
  have hmain : (a : ℝ) * Real.log (((D * k : ℕ) : ℝ) / a) ≤
      (a : ℝ) * (Real.log d + nearRegularDegreePower * Real.log (Real.log d) +
        Real.log (64 * M * A)) :=
    mul_le_mul_of_nonneg_left havailable (Nat.cast_nonneg _)
  have hoverhead := near_regular_star_overhead d k a D hd1 (by omega) hDpow hlog haverage
  have hlevel := near_regular_star_level_eq d D a hDreal hlogpos
  have hcomparison : (a : ℝ) * (Real.log d - 7 * nearRegularDegreePower * Real.log (Real.log d) +
      Real.log (64 * M * A) + 2 + nearRegularTypeError d) ≤
        (a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2) - a := by
    have h := mul_le_mul_of_nonneg_left hmargin (Nat.cast_nonneg (α := ℝ) a)
    unfold tripleLogEntropyThreshold
    nlinarith only [h]
  constructor
  · apply le_trans ?_ hcomparison
    unfold starBadTypeLogBound
    rw [hlevel]
    push_cast at hmain
    nlinarith only [hoverhead, hmain]
  · have hpair := near_regular_pair_log_lower M d k a D Δ hM hd1 hk ha hupper hlower
    have hj' : 32 * (a : ℝ) * Real.log (Real.log d) ≤ (j : ℝ) * Real.log d := by
      have heq : nearRegularLossFraction 1024 d * a / 32 =
          (32 * (a : ℝ) * Real.log (Real.log d)) / Real.log d := by
        unfold nearRegularLossFraction
        ring
      rw [heq] at hj
      exact (div_le_iff₀ hlogpos).mp hj
    have hpair' := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg (α := ℝ) j)
    have hpenalty : 8 * nearRegularDegreePower * (a : ℝ) * Real.log (Real.log d) ≤
        (j : ℝ) * Real.log (((D * k : ℕ) : ℝ) /
          ((a : ℝ) * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ))) := by
      have hcoefficient := mul_le_mul_of_nonneg_right
        (show 8 * nearRegularDegreePower ≤ (16 : ℝ) by norm_num [nearRegularDegreePower])
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) a) hloglog.le)
      nlinarith only [hpair', hj', hcoefficient]
    have hterm₁ : 0 ≤ ((tolerantTupleOrder d * k : ℕ) : ℝ) *
        Real.log ((D ^ 2 + 1 : ℕ) : ℝ) := mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D ^ 2 + 1 by omega)))
    have hterm₂ : 0 ≤ (k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ) := mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D + 1 by omega)))
    have hroot : ((2 * (k - 1) : ℕ) : ℝ) * Real.log D ≤ (a : ℝ) * nearRegularTypeError d := by
      linarith only [hoverhead, hterm₁, hterm₂]
    apply le_trans ?_ hcomparison
    unfold repeatedTypeExponent
    nlinarith only [hroot, hmain, hpenalty]

end Erdos911
