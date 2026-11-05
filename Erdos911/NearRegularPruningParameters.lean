import Erdos911.NearRegularCertificateEstimates

open Filter Asymptotics

namespace Erdos911

noncomputable def nearRegularRepeatThreshold (d : ℝ) (a : ℕ) : ℕ :=
  Nat.floor (nearRegularLossFraction 1024 d * a / 16)

noncomputable def nearRegularBlockThreshold (d : ℝ) (a : ℕ) : ℕ :=
  Nat.floor (nearRegularLossFraction 1024 d * a / 4)

noncomputable def nearRegularEffectiveDegree (d : ℝ) : ℕ :=
  Nat.floor (nearRegularLossFraction 1024 d * d / 64)

theorem near_regular_loss_parameters_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 1 ≤ d ∧ 0 < nearRegularLossFraction 1024 d ∧
      nearRegularLossFraction 1024 d ≤ 1 ∧ 1024 ≤ nearRegularLossFraction 1024 d * d := by
  have hsmall : Tendsto (fun x : ℝ => nearRegularLossFraction 1024 x) atTop (nhds 0) := by
    have h := ((Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).tendsto_div_nhds_zero).const_mul 1024
    simpa only [nearRegularLossFraction, mul_div_assoc, mul_zero, Function.comp_def, id_eq] using h
  have hlogs := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((hsmall.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))).and hlogs)
  refine ⟨max 2 (Nat.ceil x₀), ?_⟩
  intro d hd
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨hsmall, hloglog⟩ := hx₀ d
    ((Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right _ _).trans hd))
  change 1 ≤ Real.log (Real.log d) at hloglog
  have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd2)
  have hfrac : 0 < nearRegularLossFraction 1024 d := by
    unfold nearRegularLossFraction
    positivity
  refine ⟨by omega, hfrac, hsmall.le, ?_⟩
  unfold nearRegularLossFraction
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlog).mpr
  have hlogbound := Real.log_le_sub_one_of_pos hdpos
  have hscaled := mul_le_mul_of_nonneg_right hloglog hdpos.le
  nlinarith only [hlogbound, hscaled]

theorem near_regular_pruning_threshold_bounds (d k a : ℕ) (hd : 1 ≤ d) (hk : d ≤ k)
    (haverage : (d : ℝ) * k ≤ 2 * a) (hpositive : 0 < nearRegularLossFraction 1024 d)
    (hsmall : nearRegularLossFraction 1024 d ≤ 1)
    (hlarge : 1024 ≤ nearRegularLossFraction 1024 d * d) :
    4 ≤ nearRegularEffectiveDegree d ∧ nearRegularEffectiveDegree d ≤ d ∧
      nearRegularEffectiveDegree d * k ≤ 2 * nearRegularBlockThreshold d a ∧
      2 * nearRegularRepeatThreshold d a ≤ a ∧
      nearRegularLossFraction 1024 d * a / 32 ≤ (nearRegularRepeatThreshold d a : ℝ) ∧
      ((nearRegularBlockThreshold d a + 3 * nearRegularRepeatThreshold d a : ℕ) : ℝ) ≤
        nearRegularLossFraction 1024 d * a := by
  let θ := nearRegularLossFraction 1024 d
  have hθ : 0 < θ := hpositive
  have hθsmall : θ ≤ 1 := hsmall
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hdle : (d : ℝ) ≤ 2 * a := by
    have h := mul_le_mul_of_nonneg_left hkR hdR.le
    nlinarith only [h, haverage]
  have hθa : 512 ≤ θ * a := by
    have h := mul_le_mul_of_nonneg_left hdle hθ.le
    nlinarith only [h, hlarge]
  have hjlo := Nat.lt_floor_add_one (θ * a / 16)
  have hjhi := Nat.floor_le (show 0 ≤ θ * a / 16 by positivity)
  have hblo := Nat.lt_floor_add_one (θ * a / 4)
  have hbhi := Nat.floor_le (show 0 ≤ θ * a / 4 by positivity)
  have hdlo := Nat.lt_floor_add_one (θ * d / 64)
  have hdhi := Nat.floor_le (show 0 ≤ θ * d / 64 by positivity)
  change 4 ≤ Nat.floor (θ * d / 64) ∧ Nat.floor (θ * d / 64) ≤ d ∧
    Nat.floor (θ * d / 64) * k ≤ 2 * Nat.floor (θ * a / 4) ∧
    2 * Nat.floor (θ * a / 16) ≤ a ∧
    θ * a / 32 ≤ (Nat.floor (θ * a / 16) : ℝ) ∧
    ((Nat.floor (θ * a / 4) + 3 * Nat.floor (θ * a / 16) : ℕ) : ℝ) ≤ θ * a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (4 : ℝ) ≤ Nat.floor (θ * d / 64) := by nlinarith only [hdlo, hlarge]
    exact_mod_cast h
  · have hθd := mul_le_mul_of_nonneg_right hθsmall hdR.le
    have h : (Nat.floor (θ * d / 64) : ℝ) ≤ d := by nlinarith only [hdhi, hθd, hdR]
    exact_mod_cast h
  · have hdegree := mul_le_mul_of_nonneg_right hdhi (Nat.cast_nonneg (α := ℝ) k)
    have hscale := mul_le_mul_of_nonneg_left haverage hθ.le
    have h : (Nat.floor (θ * d / 64) : ℝ) * k ≤ 2 * (Nat.floor (θ * a / 4) : ℝ) := by
      nlinarith only [hdegree, hscale, hblo, hθa]
    exact_mod_cast h
  · have hθaUpper := mul_le_mul_of_nonneg_right hθsmall (Nat.cast_nonneg (α := ℝ) a)
    have h : (2 : ℝ) * Nat.floor (θ * a / 16) ≤ a := by
      nlinarith only [hjhi, hθaUpper, Nat.cast_nonneg (α := ℝ) a]
    exact_mod_cast h
  · nlinarith only [hjlo, hθa]
  · push_cast
    nlinarith only [hbhi, hjhi, hθa]

theorem near_regular_pruning_parameters_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k a : ℕ, d ≤ k → (d : ℝ) * k ≤ 2 * a →
      4 ≤ nearRegularEffectiveDegree d ∧ nearRegularEffectiveDegree d ≤ d ∧
      nearRegularEffectiveDegree d * k ≤ 2 * nearRegularBlockThreshold d a ∧
      2 * nearRegularRepeatThreshold d a ≤ a ∧
      nearRegularLossFraction 1024 d * a / 32 ≤ (nearRegularRepeatThreshold d a : ℝ) ∧
      ((nearRegularBlockThreshold d a + 3 * nearRegularRepeatThreshold d a : ℕ) : ℝ) ≤
        nearRegularLossFraction 1024 d * a := by
  obtain ⟨d₀, hd₀⟩ := near_regular_loss_parameters_uniform
  refine ⟨d₀, ?_⟩
  intro d hd k a hk haverage
  obtain ⟨hd1, hpositive, hsmall, hlarge⟩ := hd₀ d hd
  exact near_regular_pruning_threshold_bounds d k a hd1 hk haverage hpositive hsmall hlarge

end Erdos911
