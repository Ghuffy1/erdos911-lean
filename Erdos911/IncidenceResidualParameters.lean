import Erdos911.IncidenceTupleParameters
import Erdos911.NearRegularResidualParameters

open Filter

namespace Erdos911

theorem incidencePairCutoff_scale (A : ℕ) (P d : ℝ) (hd : 0 < d)
    (hlog : 0 < Real.log d) :
    nearRegularRectangleDensity d * P = incidencePairCutoff A P d *
      ((Real.log d) ^ incidenceLossPower A / d ^ (1 / 16 : ℝ)) := by
  have hp : (d ^ (1 / 16 : ℝ)) ^ 2 = d ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_mul_natCast hd.le]
    norm_num
  have hbase := Real.rpow_pos_of_pos hd (1 / 16 : ℝ)
  have hL := Real.rpow_pos_of_pos hlog (incidenceLossPower A)
  unfold nearRegularRectangleDensity incidencePairCutoff incidenceCommonCutoff
  rw [neg_div, Real.rpow_neg hd.le, ← hp]
  field_simp

theorem incidence_codegree_gap (A d : ℕ) (P : ℝ) (hd : 1 ≤ d) (hP : (d : ℝ) ≤ P)
    (hlog : 0 < Real.log d)
    (hscale : 16 * (Real.log d) ^ incidenceLossPower A ≤ (d : ℝ) ^ (1 / 16 : ℝ)) :
    0 < incidencePairCutoff A P d ∧
      2 * (nearRegularBlockSize d : ℝ) ≤ incidencePairCutoff A P d ∧
      nearRegularRectangleDensity d * P < incidencePairCutoff A P d - nearRegularBlockSize d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hPpos : 0 < P := hdR.trans_le hP
  have hR : 0 < incidencePairCutoff A P d := by
    unfold incidencePairCutoff incidenceCommonCutoff
    positivity
  have hratio : (Real.log d) ^ incidenceLossPower A / (d : ℝ) ^ (1 / 16 : ℝ) ≤ 1 / 16 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hdR _)).mpr
    linarith
  have hrho : nearRegularRectangleDensity d * P ≤ incidencePairCutoff A P d / 16 := by
    rw [incidencePairCutoff_scale A P d hdR hlog]
    exact (mul_le_mul_of_nonneg_left hratio hR.le).trans_eq (by ring)
  have hpower : (d : ℝ) * nearRegularRectangleDensity d = (d : ℝ) ^ (7 / 8 : ℝ) := by
    unfold nearRegularRectangleDensity
    calc
      _ = (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-1 / 8 : ℝ) := by rw [Real.rpow_one]
      _ = (d : ℝ) ^ ((1 : ℝ) + (-1 / 8 : ℝ)) := (Real.rpow_add hdR _ _).symm
      _ = _ := by norm_num
  have hquarter : (d : ℝ) ^ (1 / 4 : ℝ) ≤ nearRegularRectangleDensity d * P := by
    calc
      _ ≤ (d : ℝ) ^ (7 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast hd) (by norm_num)
      _ = (d : ℝ) * nearRegularRectangleDensity d := hpower.symm
      _ ≤ P * nearRegularRectangleDensity d := mul_le_mul_of_nonneg_right hP (by
        unfold nearRegularRectangleDensity; positivity)
      _ = _ := mul_comm _ _
  have hq := (nearRegularBlockSize_bounds d hd).2.2
  exact ⟨hR, by linarith, by linarith⟩

/-- Collision losses use the global degree bound `D`; the common-neighbor
cutoff and tuple supply use the local bound `P`. No comparison of `P` and
`D` is required. -/
theorem incidence_tuple_supply_gap (A : ℕ) (d D P : ℝ) (hd : 1 ≤ d)
    (hD : 0 < D) (hP : 0 < P) (hDpow : D ≤ d ^ A) (hlog : 0 < Real.log d)
    (hlarge : 2 * (4 : ℝ) ^ incidenceTupleOrder A ≤ d ^ 2) :
    D ^ 2 * (incidencePairCutoff A P d) ^ incidenceTupleOrder A ≤
      (incidenceCommonCutoff A P d / 4) ^ incidenceTupleOrder A / 2 := by
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hT : 0 < incidenceCommonCutoff A P d := by unfold incidenceCommonCutoff; positivity
  have hpower : (d ^ (1 / 16 : ℝ)) ^ incidenceTupleOrder A = d ^ (4 * (A + 1)) := by
    rw [← Real.rpow_mul_natCast hdpos.le]
    have heq : (1 / 16 : ℝ) * (incidenceTupleOrder A : ℝ) = ((4 * (A + 1) : ℕ) : ℝ) := by
      simp only [incidenceTupleOrder, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [heq, Real.rpow_natCast]
  have hD2 : D ^ 2 ≤ d ^ (2 * A) := by
    have hp := pow_le_pow_left₀ hD.le hDpow 2
    simpa only [← pow_mul, Nat.mul_comm] using hp
  have hbase : (2 * (4 : ℝ) ^ incidenceTupleOrder A) * D ^ 2 ≤ d ^ (4 * (A + 1)) := by
    calc
      _ ≤ (2 * (4 : ℝ) ^ incidenceTupleOrder A) * d ^ (2 * A) :=
        mul_le_mul_of_nonneg_left hD2 (by positivity)
      _ ≤ d ^ 2 * d ^ (2 * A) := mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = d ^ (2 + 2 * A) := (pow_add _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hd (by omega)
  unfold incidencePairCutoff
  rw [div_pow, hpower, div_pow, ← mul_div_assoc, div_div]
  apply (div_le_div_iff₀ (pow_pos hdpos _) (show 0 < (4 : ℝ) ^ incidenceTupleOrder A * 2 by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_right hbase (pow_pos hT (incidenceTupleOrder A)).le
  nlinarith only [hmul]

theorem incidence_residual_parameters_uniform (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D P : ℝ, (d : ℝ) ≤ D → D ≤ (d : ℝ) ^ A → (d : ℝ) ≤ P →
      1 ≤ nearRegularBlockSize d ∧ nearRegularBlockSize d ≤ d ∧
      0 < incidenceCommonCutoff A P d ∧ incidenceCommonCutoff A P d < P ∧
      0 < incidencePairCutoff A P d ∧ incidencePairCutoff A P d < incidenceCommonCutoff A P d ∧
      2 * (nearRegularBlockSize d : ℝ) ≤ incidencePairCutoff A P d ∧
      0 ≤ nearRegularRectangleDensity d ∧
      nearRegularRectangleDensity d * P < incidencePairCutoff A P d - nearRegularBlockSize d ∧
      D ^ 2 * (incidencePairCutoff A P d) ^ incidenceTupleOrder A ≤
        (incidenceCommonCutoff A P d / 4) ^ incidenceTupleOrder A / 2 := by
  have hlimit : Tendsto (fun x : ℝ => 16 * (Real.log x) ^ incidenceLossPower A / x ^ (1 / 16 : ℝ))
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      ((isLittleO_log_rpow_rpow_atTop (incidenceLossPower A)
        (show (0 : ℝ) < 1 / 16 by norm_num)).tendsto_div_nhds_zero).const_mul 16
  have hsmall := hlimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hsmall.and hlogs)
  refine ⟨max 2 (max (Nat.ceil x₀) (2 * 4 ^ incidenceTupleOrder A)), ?_⟩
  intro d hd D P hD hDpow hP
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDpos : 0 < D := hdpos.trans_le hD
  have hPpos : 0 < P := hdpos.trans_le hP
  have hdceil : Nat.ceil x₀ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hdceil)
  obtain ⟨hsmall, hlogs⟩ := hx₀ d hx
  have hscale : 16 * (Real.log d) ^ incidenceLossPower A ≤ (d : ℝ) ^ (1 / 16 : ℝ) := by
    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hdpos _)).mp hsmall
    linarith
  obtain ⟨hq, hqd, _⟩ := nearRegularBlockSize_bounds d (by omega)
  have hT : 0 < incidenceCommonCutoff A P d := by unfold incidenceCommonCutoff; positivity
  have hTlt : incidenceCommonCutoff A P d < P := div_lt_self hPpos
    (Real.one_lt_rpow hlogs (incidenceLossPower_pos A))
  obtain ⟨hR, hqR, hgap⟩ := incidence_codegree_gap A d P (by omega) hP (by linarith) hscale
  have hRlt : incidencePairCutoff A P d < incidenceCommonCutoff A P d := div_lt_self hT
    (Real.one_lt_rpow (by exact_mod_cast (show 1 < d by omega)) (by norm_num))
  have hlarge : 2 * (4 : ℝ) ^ incidenceTupleOrder A ≤ (d : ℝ) ^ 2 := by
    have hbound : 2 * 4 ^ incidenceTupleOrder A ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
    have hboundR : 2 * (4 : ℝ) ^ incidenceTupleOrder A ≤ d := by exact_mod_cast hbound
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    nlinarith
  exact ⟨hq, hqd, hT, hTlt, hR, hRlt, hqR, by unfold nearRegularRectangleDensity; positivity,
    hgap, incidence_tuple_supply_gap A d D P (by exact_mod_cast (show 1 ≤ d by omega))
      hDpos hPpos hDpow (by linarith) hlarge⟩

end Erdos911
