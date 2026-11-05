import Erdos911.NearRegularTupleProbability
import Erdos911.ResidualPairGraph

open Filter

namespace Erdos911

noncomputable def nearRegularBlockSize (d : ℝ) : ℕ := Nat.ceil (d ^ (1 / 4 : ℝ))

noncomputable def nearRegularPairCutoff (D d : ℝ) : ℝ :=
  nearRegularCommonCutoff D d / d ^ (1 / 16 : ℝ)

noncomputable def nearRegularRectangleDensity (d : ℝ) : ℝ := d ^ (-1 / 8 : ℝ)

theorem nearRegularBlockSize_bounds (d : ℕ) (hd : 1 ≤ d) :
    1 ≤ nearRegularBlockSize d ∧ nearRegularBlockSize d ≤ d ∧
      (nearRegularBlockSize d : ℝ) ≤ 2 * (d : ℝ) ^ (1 / 4 : ℝ) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : 1 ≤ (d : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hdR (by norm_num)
  have hle : (d : ℝ) ^ (1 / 4 : ℝ) ≤ d := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hdR
      (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · change 1 ≤ Nat.ceil ((d : ℝ) ^ (1 / 4 : ℝ))
    exact_mod_cast hpow.trans (Nat.le_ceil _)
  · exact Nat.ceil_le.mpr hle
  · have hc := (Nat.ceil_lt_add_one (show 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) by positivity)).le
    change (Nat.ceil ((d : ℝ) ^ (1 / 4 : ℝ)) : ℝ) ≤ _
    linarith

theorem nearRegularPairCutoff_scale (D d : ℝ) (hd : 0 < d) (hlog : 0 < Real.log d) :
    nearRegularRectangleDensity d * D = nearRegularPairCutoff D d *
      ((Real.log d) ^ nearRegularLossPower / d ^ (1 / 16 : ℝ)) := by
  have hp : (d ^ (1 / 16 : ℝ)) ^ 2 = d ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_mul_natCast hd.le]
    norm_num
  have hbase := Real.rpow_pos_of_pos hd (1 / 16 : ℝ)
  have hL := Real.rpow_pos_of_pos hlog nearRegularLossPower
  unfold nearRegularRectangleDensity nearRegularPairCutoff nearRegularCommonCutoff
  rw [neg_div, Real.rpow_neg hd.le, ← hp]
  field_simp

theorem near_regular_codegree_gap (d : ℕ) (D : ℝ) (hd : 1 ≤ d) (hD : (d : ℝ) ≤ D)
    (hlog : 0 < Real.log d)
    (hscale : 16 * (Real.log d) ^ nearRegularLossPower ≤ (d : ℝ) ^ (1 / 16 : ℝ)) :
    0 < nearRegularPairCutoff D d ∧
      2 * (nearRegularBlockSize d : ℝ) ≤ nearRegularPairCutoff D d ∧
      nearRegularRectangleDensity d * D < nearRegularPairCutoff D d - nearRegularBlockSize d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDpos : 0 < D := hdR.trans_le hD
  have hR : 0 < nearRegularPairCutoff D d := by
    unfold nearRegularPairCutoff nearRegularCommonCutoff
    positivity
  have hratio : (Real.log d) ^ nearRegularLossPower / (d : ℝ) ^ (1 / 16 : ℝ) ≤ 1 / 16 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hdR _)).mpr
    linarith
  have hrho : nearRegularRectangleDensity d * D ≤ nearRegularPairCutoff D d / 16 := by
    rw [nearRegularPairCutoff_scale D d hdR hlog]
    exact (mul_le_mul_of_nonneg_left hratio hR.le).trans_eq (by ring)
  have hpower : (d : ℝ) * nearRegularRectangleDensity d = (d : ℝ) ^ (7 / 8 : ℝ) := by
    unfold nearRegularRectangleDensity
    calc
      _ = (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-1 / 8 : ℝ) := by rw [Real.rpow_one]
      _ = (d : ℝ) ^ ((1 : ℝ) + (-1 / 8 : ℝ)) := (Real.rpow_add hdR _ _).symm
      _ = _ := by norm_num
  have hquarter : (d : ℝ) ^ (1 / 4 : ℝ) ≤ nearRegularRectangleDensity d * D := by
    calc
      _ ≤ (d : ℝ) ^ (7 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hd) (by norm_num)
      _ = (d : ℝ) * nearRegularRectangleDensity d := hpower.symm
      _ ≤ D * nearRegularRectangleDensity d := mul_le_mul_of_nonneg_right hD (by
        unfold nearRegularRectangleDensity; positivity)
      _ = _ := mul_comm _ _
  have hq := (nearRegularBlockSize_bounds d hd).2.2
  refine ⟨hR, ?_, ?_⟩ <;> linarith

theorem near_regular_tuple_supply_gap (d D : ℝ) (hd : 1 ≤ d) (hD : 0 < D) (hDpow : D ≤ d ^ 3)
    (hlog : 0 < Real.log d) (hlarge : 2 * (4 : ℝ) ^ 128 ≤ d ^ 2) :
    D ^ 2 * (nearRegularPairCutoff D d) ^ 128 ≤ (nearRegularCommonCutoff D d / 4) ^ 128 / 2 := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hT : 0 < nearRegularCommonCutoff D d := by unfold nearRegularCommonCutoff; positivity
  have hpower : (d ^ (1 / 16 : ℝ)) ^ 128 = d ^ 8 := by
    rw [← Real.rpow_mul_natCast hdpos.le]
    norm_num [Real.rpow_natCast]
  have hD2 : D ^ 2 ≤ d ^ 6 := by
    have hp := pow_le_pow_left₀ hD.le hDpow 2
    simpa only [← pow_mul] using hp
  have hbase : (2 * (4 : ℝ) ^ 128) * D ^ 2 ≤ d ^ 8 := by
    calc
      _ ≤ (2 * (4 : ℝ) ^ 128) * d ^ 6 := mul_le_mul_of_nonneg_left hD2 (by positivity)
      _ ≤ d ^ 2 * d ^ 6 := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = d ^ 8 := by ring
  unfold nearRegularPairCutoff
  rw [div_pow, hpower, div_pow, ← mul_div_assoc, div_div]
  apply (div_le_div_iff₀ (pow_pos hdpos 8) (show 0 < (4 : ℝ) ^ 128 * 2 by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_right hbase (pow_pos hT 128).le
  nlinarith only [hmul]

theorem near_regular_residual_parameters_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D : ℝ, (d : ℝ) ≤ D → D ≤ (d : ℝ) ^ 3 →
      1 ≤ nearRegularBlockSize d ∧ nearRegularBlockSize d ≤ d ∧
      0 < nearRegularCommonCutoff D d ∧ nearRegularCommonCutoff D d < D ∧
      0 < nearRegularPairCutoff D d ∧ nearRegularPairCutoff D d < nearRegularCommonCutoff D d ∧
      2 * (nearRegularBlockSize d : ℝ) ≤ nearRegularPairCutoff D d ∧
      0 ≤ nearRegularRectangleDensity d ∧
      nearRegularRectangleDensity d * D < nearRegularPairCutoff D d - nearRegularBlockSize d ∧
      D ^ 2 * (nearRegularPairCutoff D d) ^ 128 ≤ (nearRegularCommonCutoff D d / 4) ^ 128 / 2 := by
  have hlimit : Tendsto (fun x : ℝ => 16 * (Real.log x) ^ nearRegularLossPower / x ^ (1 / 16 : ℝ))
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      ((isLittleO_log_rpow_rpow_atTop nearRegularLossPower
        (show (0 : ℝ) < 1 / 16 by norm_num)).tendsto_div_nhds_zero).const_mul 16
  have hsmall := hlimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hsmall.and hlogs)
  refine ⟨max 2 (max (Nat.ceil x₀) (2 * 4 ^ 128)), ?_⟩
  intro d hd D hD hDpow
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDpos : 0 < D := hdpos.trans_le hD
  have hdceil : Nat.ceil x₀ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hdceil)
  obtain ⟨hsmall, hlogs⟩ := hx₀ d hx
  have hscale : 16 * (Real.log d) ^ nearRegularLossPower ≤ (d : ℝ) ^ (1 / 16 : ℝ) := by
    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hdpos _)).mp hsmall
    linarith
  obtain ⟨hq, hqd, _⟩ := nearRegularBlockSize_bounds d (by omega)
  have hT : 0 < nearRegularCommonCutoff D d := by unfold nearRegularCommonCutoff; positivity
  have hTlt : nearRegularCommonCutoff D d < D := div_lt_self hDpos
    (Real.one_lt_rpow hlogs (by norm_num [nearRegularLossPower]))
  obtain ⟨hR, hqR, hgap⟩ := near_regular_codegree_gap d D (by omega) hD (by linarith) hscale
  have hRlt : nearRegularPairCutoff D d < nearRegularCommonCutoff D d := div_lt_self hT
    (Real.one_lt_rpow (by exact_mod_cast (show 1 < d by omega)) (by norm_num))
  have hlarge : 2 * (4 : ℝ) ^ 128 ≤ (d : ℝ) ^ 2 := by
    have hbound : 2 * 4 ^ 128 ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
    have hboundR : (2 * (4 : ℝ) ^ 128) ≤ d := by exact_mod_cast hbound
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    nlinarith
  exact ⟨hq, hqd, hT, hTlt, hR, hRlt, hqR, by unfold nearRegularRectangleDensity; positivity,
    hgap, near_regular_tuple_supply_gap d D (by exact_mod_cast (show 1 ≤ d by omega)) hDpos hDpow
      (by linarith) hlarge⟩

end Erdos911
