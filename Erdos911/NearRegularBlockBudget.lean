import Erdos911.NearRegularPruningParameters
import Erdos911.NearRegularTypeGaps

open Filter Asymptotics

namespace Erdos911

noncomputable def nearRegularBlockRate (d : ℝ) : ℝ := 16 * (Real.log d) ^ 2 / d

noncomputable def nearRegularBlockCost (M C d : ℝ) : ℝ :=
  256 * M * C / Real.log d + 64 * M * C * (Real.log d) ^ 3 / d ^ (1 / 8 : ℝ)

theorem near_regular_effective_degree_lower (d : ℝ) (hd : 0 < d)
    (hlog : 0 < Real.log d) (hloglog : 1 ≤ Real.log (Real.log d))
    (hlarge : 1024 ≤ nearRegularLossFraction 1024 d * d) :
    8 * d / Real.log d ≤ (nearRegularEffectiveDegree d : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (nearRegularLossFraction 1024 d * d / 64)
  have hhalf : nearRegularLossFraction 1024 d * d / 128 ≤ (nearRegularEffectiveDegree d : ℝ) := by
    unfold nearRegularEffectiveDegree
    nlinarith only [hfloor, hlarge]
  apply le_trans ?_ hhalf
  unfold nearRegularLossFraction
  have hscaled := mul_le_mul_of_nonneg_right hloglog hd.le
  calc
    8 * d / Real.log d ≤ 8 * Real.log (Real.log d) * d / Real.log d :=
      div_le_div_of_nonneg_right (by nlinarith only [hscaled]) hlog.le
    _ = _ := by ring

theorem near_regular_block_rate_scale (d D : ℕ) (hd : 1 ≤ d) (hD : 0 < D)
    (hDpow : D ≤ d ^ 3) (hlog : 0 < Real.log d) (hloglog : 1 ≤ Real.log (Real.log d))
    (hlarge : 1024 ≤ nearRegularLossFraction 1024 d * d) :
    32 * Real.log D ≤ nearRegularBlockRate d * nearRegularEffectiveDegree d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hlogD : Real.log D ≤ 3 * Real.log d := by
    apply (Real.log_le_log hDpos (show (D : ℝ) ≤ (d : ℝ) ^ 3 by exact_mod_cast hDpow)).trans_eq
    rw [Real.log_pow]
    norm_num
  have hp : 0 ≤ nearRegularBlockRate d := by unfold nearRegularBlockRate; positivity
  have hlower := mul_le_mul_of_nonneg_left
    (near_regular_effective_degree_lower d hdpos hlog hloglog hlarge) hp
  have heq : nearRegularBlockRate d * (8 * d / Real.log d) = 128 * Real.log d := by
    unfold nearRegularBlockRate
    field_simp
    ring
  rw [heq] at hlower
  linarith only [hlower, hlogD, hlog]

theorem near_regular_two_scale_budget (M C d m E : ℝ)
    (hC : 0 ≤ C) (hd : 0 < d) (hlog : 0 < Real.log d)
    (hm : 0 ≤ m) (hhost : m ≤ M * d * E) :
    (2 * nearRegularBlockRate d) *
        (2 * (C * Real.log d) * m / ((1 / 4 : ℝ) * baselineBlockSize d) +
          2 * (C * Real.log d) * m / (nearRegularRectangleDensity d * nearRegularBlockSize d)) ≤
      nearRegularBlockCost M C d * E := by
  have hq₁ : (Real.log d) ^ 4 ≤ (baselineBlockSize d : ℝ) := Nat.le_ceil _
  have hq₂ : d ^ (1 / 4 : ℝ) ≤ (nearRegularBlockSize d : ℝ) := Nat.le_ceil _
  have hρ : 0 < nearRegularRectangleDensity d := by unfold nearRegularRectangleDensity; positivity
  have hden₁ : (1 / 4 : ℝ) * (Real.log d) ^ 4 ≤ (1 / 4 : ℝ) * baselineBlockSize d := by linarith
  have hden₂ : d ^ (1 / 8 : ℝ) ≤ nearRegularRectangleDensity d * nearRegularBlockSize d := by
    calc
      _ = nearRegularRectangleDensity d * d ^ (1 / 4 : ℝ) := by
        unfold nearRegularRectangleDensity
        rw [← Real.rpow_add hd]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hq₂ hρ.le
  have hn : 0 ≤ 2 * (C * Real.log d) * m := by positivity
  have hnHost := mul_le_mul_of_nonneg_left hhost (show 0 ≤ 2 * (C * Real.log d) by positivity)
  have hfirst : 2 * (C * Real.log d) * m / ((1 / 4 : ℝ) * baselineBlockSize d) ≤
      2 * (C * Real.log d) * (M * d * E) / ((1 / 4 : ℝ) * (Real.log d) ^ 4) := by
    exact (div_le_div_of_nonneg_left hn (by positivity) hden₁).trans
      (div_le_div_of_nonneg_right hnHost (by positivity))
  have hsecond : 2 * (C * Real.log d) * m / (nearRegularRectangleDensity d * nearRegularBlockSize d) ≤
      2 * (C * Real.log d) * (M * d * E) / d ^ (1 / 8 : ℝ) := by
    exact (div_le_div_of_nonneg_left hn (Real.rpow_pos_of_pos hd _) hden₂).trans
      (div_le_div_of_nonneg_right hnHost (Real.rpow_nonneg hd.le _))
  have hp : 0 ≤ 2 * nearRegularBlockRate d := by unfold nearRegularBlockRate; positivity
  calc
    _ ≤ (2 * nearRegularBlockRate d) *
        (2 * (C * Real.log d) * (M * d * E) / ((1 / 4 : ℝ) * (Real.log d) ^ 4) +
          2 * (C * Real.log d) * (M * d * E) / d ^ (1 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hp
    _ = _ := by
      unfold nearRegularBlockRate nearRegularBlockCost
      field_simp
      ring

theorem nearRegularBlockRate_tends_to_zero :
    Tendsto nearRegularBlockRate atTop (nhds 0) := by
  have h := nearRegularTypeError_tends_to_zero.div_const 4
  convert h using 1
  · funext x
    unfold nearRegularBlockRate nearRegularTypeError
    ring
  · norm_num

theorem nearRegularBlockCost_tends_to_zero (M C : ℝ) :
    Tendsto (nearRegularBlockCost M C) atTop (nhds 0) := by
  have hfirst := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (256 * M * C)
  have hsecond := ((isLittleO_log_rpow_rpow_atTop (3 : ℕ)
    (show (0 : ℝ) < 1 / 8 by norm_num)).tendsto_div_nhds_zero).const_mul (64 * M * C)
  have h := hfirst.add hsecond
  simp only [mul_zero, add_zero, Real.rpow_natCast] at h
  convert h using 1
  funext x
  unfold nearRegularBlockCost
  simp only [Function.comp_def]
  ring

theorem near_regular_block_parameters_uniform (M C : ℝ) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D : ℕ, d ≤ D → D ≤ d ^ 3 →
      0 ≤ nearRegularBlockRate d ∧ nearRegularBlockRate d ≤ 1 ∧
      32 * Real.log D ≤ nearRegularBlockRate d * nearRegularEffectiveDegree d ∧
      ∀ m E : ℝ, 0 ≤ m → 0 ≤ E → m ≤ M * d * E →
        (2 * nearRegularBlockRate d) *
            (2 * (C * Real.log d) * m / ((1 / 4 : ℝ) * baselineBlockSize d) +
              2 * (C * Real.log d) * m / (nearRegularRectangleDensity d * nearRegularBlockSize d)) ≤
          (1 / 16 : ℝ) * E := by
  obtain ⟨dL, hdL⟩ := near_regular_loss_parameters_uniform
  have hp := nearRegularBlockRate_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hcost := (nearRegularBlockCost_tends_to_zero M C).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
  have hlogs := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hp.and (hcost.and hlogs))
  refine ⟨max 2 (max dL (Nat.ceil x₀)), ?_⟩
  intro d hd D hdD hDpow
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog : 0 < Real.log d := Real.log_pos (by exact_mod_cast hd2)
  obtain ⟨_, _, _, hlarge⟩ := hdL d (by omega)
  obtain ⟨hp, hcost, hloglog⟩ := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast (show Nat.ceil x₀ ≤ d by omega)))
  refine ⟨by unfold nearRegularBlockRate; positivity, hp.le,
    near_regular_block_rate_scale d D (by omega) (by omega) hDpow hlog hloglog hlarge, ?_⟩
  intro m E hm hE hhost
  exact (near_regular_two_scale_budget M C d m E hC hdpos hlog hm hhost).trans
    (mul_le_mul_of_nonneg_right hcost.le hE)

end Erdos911
