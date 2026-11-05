import Erdos911.IncidenceSamplingParameters
import Erdos911.NearRegularCertificateEstimates
import Erdos911.BaselineResidualParameters

open Filter

namespace Erdos911

noncomputable def incidenceExceptionCoefficient (A : ℕ) (B d : ℝ) : ℝ :=
  (5 * baselineSampleConstant A) * (Real.log d) ^ (9 / 4 : ℝ) / d +
    8 * B * Real.log (Real.log d) * (Real.log d) ^ (-1 / 4 : ℝ)

theorem incidenceExceptionCoefficient_identity (A : ℕ) (B d : ℝ) (hd : 0 < d)
    (hlog : 0 < Real.log d) :
    ((5 * baselineSampleConstant A) * (Real.log d) ^ 2 / d +
      8 * nearRegularLossFraction B d / tolerantSamplingError d) *
        (Real.log d) ^ (1 / 4 : ℝ) = incidenceExceptionCoefficient A B d := by
  let L := Real.log d
  have hL : 0 < L := hlog
  have hseed : L ^ 2 * L ^ (1 / 4 : ℝ) = L ^ (9 / 4 : ℝ) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL]
    norm_num
  have hloss : (Real.sqrt L * L ^ (1 / 4 : ℝ)) / L = L ^ (-1 / 4 : ℝ) := by
    calc
      _ = L ^ (1 / 2 + 1 / 4 : ℝ) / L ^ (1 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL, Real.rpow_one]
      _ = L ^ (1 / 2 + 1 / 4 - 1 : ℝ) := (Real.rpow_sub hL _ _).symm
      _ = _ := by norm_num
  calc
    _ = (5 * baselineSampleConstant A) * (L ^ 2 * L ^ (1 / 4 : ℝ)) / d +
        8 * B * Real.log L * ((Real.sqrt L * L ^ (1 / 4 : ℝ)) / L) := by
      unfold nearRegularLossFraction tolerantSamplingError
      dsimp only [L]
      have hsqrt := Real.sqrt_pos.mpr hlog
      field_simp
    _ = _ := by rw [hseed, hloss]; rfl

theorem incidenceExceptionCoefficient_tends_to_zero (A : ℕ) (B : ℝ) :
    Tendsto (incidenceExceptionCoefficient A B) atTop (nhds 0) := by
  have hseed := (isLittleO_log_rpow_rpow_atTop (9 / 4 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  have hloss := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
  have hloss' : Tendsto (fun x : ℝ => Real.log x * x ^ (-1 / 4 : ℝ)) atTop (nhds 0) := by
    apply hloss.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [neg_div, Real.rpow_neg hx.le, div_eq_mul_inv]
  have h := (hseed.const_mul (5 * baselineSampleConstant A)).add
    ((hloss'.comp Real.tendsto_log_atTop).const_mul (8 * B))
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext x
  unfold incidenceExceptionCoefficient
  simp only [Function.comp_def, Real.rpow_one]
  ring

theorem incidence_certificate_estimate_parameters (A : ℕ) (B : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 1 ≤ d ∧ 1 ≤ Real.log d ∧
      4 ≤ (Real.log d) ^ (1 / 16 : ℝ) ∧ incidenceExceptionCoefficient A B d ≤ 1 / 8 := by
  have hcoef := (incidenceExceptionCoefficient_tends_to_zero A B).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  have hpower := ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 16 by norm_num)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop (4 : ℝ))
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hcoef.and (hpower.and hlog))
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd
  obtain ⟨hc, hp, hl⟩ := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right _ _).trans hd))
  exact ⟨(le_max_left _ _).trans hd, hl, hp, hc.le⟩

theorem incidence_certificate_budgets (A : ℕ) (B d : ℝ) (k : ℕ) (e loss seed : ℝ)
    (hB : 0 ≤ B) (hd : 0 < d) (hlog : 1 ≤ Real.log d)
    (he : e ≤ d * k) (hloss₀ : 0 ≤ loss) (hseed₀ : 0 ≤ seed)
    (hloss : loss ≤ nearRegularLossFraction B d * e)
    (hseed : seed ≤ (5 * baselineSampleConstant A) * k * (Real.log d) ^ 2 / d)
    (hcoef : incidenceExceptionCoefficient A B d ≤ 1 / 8)
    (hpower : 4 ≤ (Real.log d) ^ (1 / 16 : ℝ)) :
    seed + 8 * loss / (tolerantSamplingError d * d) ≤ (k : ℝ) / 8 ∧
      4 * loss / (tolerantSamplingError d * d) ≤ nearRegularExceptionBound d k ∧
      (nearRegularMatchingSize d k : ℝ) ≤ (k : ℝ) / 4 := by
  have hL : 0 < Real.log d := by linarith
  have hε : 0 < tolerantSamplingError d := tolerantSamplingError_pos d hL
  have hquarter : 0 < (Real.log d) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL _
  have hquarter1 : 1 ≤ (Real.log d) ^ (1 / 4 : ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hθ : 0 ≤ nearRegularLossFraction B d := by
    unfold nearRegularLossFraction
    exact div_nonneg (mul_nonneg hB (Real.log_nonneg hlog)) hL.le
  have hloss' : loss ≤ nearRegularLossFraction B d * (d * k) :=
    hloss.trans (mul_le_mul_of_nonneg_left he hθ)
  let C := (5 * baselineSampleConstant A) * (Real.log d) ^ 2 / d +
    8 * nearRegularLossFraction B d / tolerantSamplingError d
  have hC : C ≤ 1 / (8 * (Real.log d) ^ (1 / 4 : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hidentity := incidenceExceptionCoefficient_identity A B d hd hL
    change C * (Real.log d) ^ (1 / 4 : ℝ) = _ at hidentity
    nlinarith only [hidentity, hcoef]
  have hscaled : seed + 8 * loss / (tolerantSamplingError d * d) ≤
      (k : ℝ) / (8 * (Real.log d) ^ (1 / 4 : ℝ)) := by
    calc
      _ ≤ (5 * baselineSampleConstant A) * k * (Real.log d) ^ 2 / d +
          8 * (nearRegularLossFraction B d * (d * k)) / (tolerantSamplingError d * d) :=
        add_le_add hseed (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hloss' (by norm_num)) (by positivity))
      _ = (k : ℝ) * C := by dsimp only [C]; field_simp
      _ ≤ (k : ℝ) * (1 / (8 * (Real.log d) ^ (1 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg k)
      _ = _ := by ring
  have hsmall : seed + 8 * loss / (tolerantSamplingError d * d) ≤ (k : ℝ) / 8 := by
    apply hscaled.trans
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by norm_num) (by linarith)
  have hexception : 4 * loss / (tolerantSamplingError d * d) ≤ nearRegularExceptionBound d k := by
    have hnonneg : 0 ≤ 4 * loss / (tolerantSamplingError d * d) := by positivity
    have hfirst : 4 * loss / (tolerantSamplingError d * d) ≤
        seed + 8 * loss / (tolerantSamplingError d * d) := by
      have heq : 8 * loss / (tolerantSamplingError d * d) =
          2 * (4 * loss / (tolerantSamplingError d * d)) := by ring
      rw [heq]
      linarith only [hnonneg, hseed₀]
    apply (hfirst.trans hscaled).trans
    unfold nearRegularExceptionBound
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg k) hquarter (by nlinarith only [hquarter])
  have hmatching : (nearRegularMatchingSize d k : ℝ) ≤ (k : ℝ) / 4 := by
    have hfloor : (nearRegularMatchingSize d k : ℝ) ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ) :=
      Nat.floor_le (by positivity)
    exact hfloor.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by norm_num) hpower)
  exact ⟨hsmall, hexception, hmatching⟩

theorem incidence_matching_mass_of_budgets (d : ℝ) (k m : ℕ) (b e bad orient seed cost : ℝ)
    (hd : 0 < d) (hbalance : e = d * b) (hhalf : (k : ℝ) / 2 ≤ b)
    (hbad : d * bad ≤ e / 8) (horient : d * orient ≤ e / 32)
    (hbudget : seed + cost ≤ (k : ℝ) / 8)
    (hmatching : b ≤ m + bad + orient + seed + cost)
    (hsmall : (nearRegularMatchingSize d k : ℝ) ≤ (k : ℝ) / 4) :
    nearRegularMatchingSize d k ≤ m := by
  have hbad' : bad ≤ b / 8 := by nlinarith only [hbalance, hbad, hd]
  have horient' : orient ≤ b / 32 := by nlinarith only [hbalance, horient, hd]
  have hm : (nearRegularMatchingSize d k : ℝ) ≤ m := by
    nlinarith only [hbad', horient', hbudget, hmatching, hhalf, hsmall, Nat.cast_nonneg (α := ℝ) k]
  exact_mod_cast hm

theorem incidence_first_scale_parameters_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 0 < d ∧ 0 < baselineBlockSize d ∧
      8 * baselineBlockSize d ≤ d ∧ tolerantSamplingError d < 1 / 20 ∧
      (1 / 4 : ℝ) * d + 4 * baselineBlockSize d < (1 - 5 * tolerantSamplingError d) * d := by
  have hq := baselineBlockSize_ratio_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
  have hε := tolerantSamplingError_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 20 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hq.and hε)
  obtain ⟨dB, hdB⟩ := eventually_baseline_residual_bounds 1
  refine ⟨max dB (max 1 (Nat.ceil x₀)), ?_⟩
  intro d hd
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  obtain ⟨hsmall, hεsmall⟩ := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast (show Nat.ceil x₀ ≤ d by omega)))
  obtain ⟨_, _, _, _, _, _, hqpos, _⟩ := hdB d (by omega)
  have hqsmall : (baselineBlockSize d : ℝ) < d / 16 := by
    have h := (div_lt_iff₀ hdR).mp hsmall
    linarith only [h]
  have hgap := mul_lt_mul_of_pos_right hεsmall hdR
  exact ⟨hdpos, by omega, by exact_mod_cast (show (8 : ℝ) * baselineBlockSize d ≤ d by linarith),
    hεsmall, by nlinarith only [hqsmall, hgap, hdR]⟩

end Erdos911
