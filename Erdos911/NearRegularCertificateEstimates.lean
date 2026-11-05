import Erdos911.NearRegularMatchingParameters
import Erdos911.TolerantSamplingParameters

open Filter

namespace Erdos911

noncomputable def nearRegularDegreePower : ℝ := 1 / 100000000

noncomputable def nearRegularLossFraction (B d : ℝ) : ℝ :=
  B * Real.log (Real.log d) / Real.log d

noncomputable def nearRegularExceptionCoefficient (A B d : ℝ) : ℝ :=
  (5 * baselineSampleConstant 3) * (Real.log d) ^ (9 / 4 : ℝ) / d +
    (A * B / 2) * Real.log (Real.log d) * (Real.log d) ^ (nearRegularDegreePower - 1 / 4)

theorem nearRegularExceptionCoefficient_identity (A B d : ℝ) (hd : 0 < d) (hlog : 0 < Real.log d) :
    ((5 * baselineSampleConstant 3) * (Real.log d) ^ 2 / d +
      nearRegularLossFraction B d * (A * (Real.log d) ^ nearRegularDegreePower) /
        (2 * tolerantSamplingError d)) * (Real.log d) ^ (1 / 4 : ℝ) =
      nearRegularExceptionCoefficient A B d := by
  let L := Real.log d
  have hL : 0 < L := hlog
  have hseed : L ^ 2 * L ^ (1 / 4 : ℝ) = L ^ (9 / 4 : ℝ) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL]
    norm_num
  have hloss : (L ^ nearRegularDegreePower * Real.sqrt L * L ^ (1 / 4 : ℝ)) / L =
      L ^ (nearRegularDegreePower - 1 / 4) := by
    calc
      _ = L ^ (nearRegularDegreePower + 1 / 2 + 1 / 4) / L ^ (1 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL, ← Real.rpow_add hL, Real.rpow_one]
      _ = L ^ (nearRegularDegreePower + 1 / 2 + 1 / 4 - 1) := (Real.rpow_sub hL _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (5 * baselineSampleConstant 3) * (L ^ 2 * L ^ (1 / 4 : ℝ)) / d +
        (A * B / 2) * Real.log L * ((L ^ nearRegularDegreePower * Real.sqrt L * L ^ (1 / 4 : ℝ)) / L) := by
      unfold nearRegularLossFraction tolerantSamplingError
      dsimp only [L]
      have hsqrt := Real.sqrt_pos.mpr hlog
      field_simp
    _ = _ := by rw [hseed, hloss]; rfl

/-- The near-regular degree and edge-loss bounds imply all three numeric
budgets used by the sampled copy certificate. -/
theorem near_regular_certificate_budgets (A B d : ℝ) (k : ℕ) (Δ a loss s : ℝ)
    (hB : 0 ≤ B) (hd : 0 < d) (hlog : 1 ≤ Real.log d) (hΔ : 0 ≤ Δ)
    (hdegree : Δ ≤ A * d * (Real.log d) ^ nearRegularDegreePower)
    (hmin : d * k / 2 ≤ a) (hmax : a ≤ Δ * k / 2)
    (hloss : loss ≤ nearRegularLossFraction B d * a)
    (hseed : s ≤ (5 * baselineSampleConstant 3) * k * (Real.log d) ^ 2 / d)
    (hmatch : 2 * A * (Real.log d) ^ nearRegularDegreePower ≤ (Real.log d) ^ (1 / 16 : ℝ))
    (hcost : 8 * A * (Real.log d) ^ nearRegularDegreePower ≤ (Real.log d) ^ (1 / 4 : ℝ))
    (hsmall : nearRegularExceptionCoefficient A B d ≤ 1) :
    (nearRegularMatchingSize d k : ℝ) * Δ ≤ a ∧
      s + loss / (tolerantSamplingError d * d) ≤ nearRegularExceptionBound d k ∧
      2 * Δ * (s + loss / (tolerantSamplingError d * d)) ≤ a / 2 := by
  have hL : 0 < Real.log d := by linarith
  have he : 0 < tolerantSamplingError d := tolerantSamplingError_pos d hL
  have h16 : 0 < (Real.log d) ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos hL _
  have hquarter : 0 < (Real.log d) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hL _
  have hLossNonneg : 0 ≤ nearRegularLossFraction B d := by
    unfold nearRegularLossFraction
    exact div_nonneg (mul_nonneg hB (Real.log_nonneg hlog)) hL.le
  have hΔmatch : Δ ≤ d * (Real.log d) ^ (1 / 16 : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left hmatch hd.le
    nlinarith only [h, hdegree]
  have hmatching : (nearRegularMatchingSize d k : ℝ) * Δ ≤ a := by
    have hfloor : (nearRegularMatchingSize d k : ℝ) ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ) :=
      Nat.floor_le (by positivity)
    calc
      _ ≤ ((k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ)) * Δ := mul_le_mul_of_nonneg_right hfloor hΔ
      _ ≤ ((k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ)) * (d * (Real.log d) ^ (1 / 16 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hΔmatch (by positivity)
      _ = d * k / 2 := by field_simp
      _ ≤ a := hmin
  let E := (5 * baselineSampleConstant 3) * (Real.log d) ^ 2 / d +
    nearRegularLossFraction B d * (A * (Real.log d) ^ nearRegularDegreePower) / (2 * tolerantSamplingError d)
  have hE : E ≤ 1 / (Real.log d) ^ (1 / 4 : ℝ) := by
    apply (le_div_iff₀ hquarter).mpr
    exact (nearRegularExceptionCoefficient_identity A B d hd hL).le.trans hsmall
  have hloss' : loss ≤ nearRegularLossFraction B d * (A * d * (Real.log d) ^ nearRegularDegreePower) * k / 2 := by
    apply hloss.trans
    apply (mul_le_mul_of_nonneg_left hmax hLossNonneg).trans
    have h := mul_le_mul_of_nonneg_left hdegree (mul_nonneg hLossNonneg (Nat.cast_nonneg k))
    nlinarith only [h]
  have hexception : s + loss / (tolerantSamplingError d * d) ≤ nearRegularExceptionBound d k := by
    calc
      _ ≤ (5 * baselineSampleConstant 3) * k * (Real.log d) ^ 2 / d +
          (nearRegularLossFraction B d * (A * d * (Real.log d) ^ nearRegularDegreePower) * k / 2) /
            (tolerantSamplingError d * d) :=
        add_le_add hseed (div_le_div_of_nonneg_right hloss' (mul_nonneg he.le hd.le))
      _ = (k : ℝ) * E := by dsimp only [E]; field_simp
      _ ≤ (k : ℝ) * (1 / (Real.log d) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg k)
      _ = _ := by unfold nearRegularExceptionBound; ring
  have hΔcost : 8 * Δ ≤ d * (Real.log d) ^ (1 / 4 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hcost hd.le
    nlinarith only [h, hdegree]
  have hcapacity : 2 * Δ * nearRegularExceptionBound d k ≤ a / 2 := by
    have hscale := mul_le_mul_of_nonneg_right hΔcost (Nat.cast_nonneg (α := ℝ) k)
    have hcap : 2 * Δ * nearRegularExceptionBound d k ≤ d * k / 4 := by
      unfold nearRegularExceptionBound
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hquarter).mpr
      nlinarith only [hscale]
    exact hcap.trans (by linarith only [hmin])
  exact ⟨hmatching, hexception,
    (mul_le_mul_of_nonneg_left hexception (by positivity : 0 ≤ 2 * Δ)).trans hcapacity⟩

theorem nearRegularExceptionCoefficient_tends_to_zero (A B : ℝ) :
    Tendsto (nearRegularExceptionCoefficient A B) atTop (nhds 0) := by
  have hseed := (isLittleO_log_rpow_rpow_atTop (9 / 4 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  have hgap : 0 < 1 / 4 - nearRegularDegreePower := by norm_num [nearRegularDegreePower]
  have hloss := (isLittleO_log_rpow_atTop hgap).tendsto_div_nhds_zero
  have hloss' : Tendsto (fun x : ℝ => Real.log x * x ^ (nearRegularDegreePower - 1 / 4))
      atTop (nhds 0) := by
    apply hloss.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show nearRegularDegreePower - 1 / 4 = -(1 / 4 - nearRegularDegreePower) by ring,
      Real.rpow_neg hx.le, div_eq_mul_inv]
  have h := (hseed.const_mul (5 * baselineSampleConstant 3)).add
    ((hloss'.comp Real.tendsto_log_atTop).const_mul (A * B / 2))
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext x
  unfold nearRegularExceptionCoefficient
  simp only [Function.comp_def, Real.rpow_one]
  ring

theorem near_regular_certificate_estimates_uniform (A B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (k : ℕ) (Δ a loss s : ℝ),
      0 ≤ Δ → Δ ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
      (d : ℝ) * k / 2 ≤ a → a ≤ Δ * k / 2 →
      loss ≤ nearRegularLossFraction B d * a →
      s ≤ (5 * baselineSampleConstant 3) * k * (Real.log d) ^ 2 / d →
      (nearRegularMatchingSize d k : ℝ) * Δ ≤ a ∧
      s + loss / (tolerantSamplingError d * d) ≤ nearRegularExceptionBound d k ∧
      2 * Δ * (s + loss / (tolerantSamplingError d * d)) ≤ a / 2 := by
  have h16 : 0 < 1 / 16 - nearRegularDegreePower := by norm_num [nearRegularDegreePower]
  have h4 : 0 < 1 / 4 - nearRegularDegreePower := by norm_num [nearRegularDegreePower]
  have hm : Tendsto (fun x : ℝ => 2 * A * (Real.log x) ^ (nearRegularDegreePower - 1 / 16))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, neg_sub] using
      ((tendsto_rpow_neg_atTop h16).comp Real.tendsto_log_atTop).const_mul (2 * A)
  have hc : Tendsto (fun x : ℝ => 8 * A * (Real.log x) ^ (nearRegularDegreePower - 1 / 4))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero, neg_sub] using
      ((tendsto_rpow_neg_atTop h4).comp Real.tendsto_log_atTop).const_mul (8 * A)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((hm.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))).and
      ((hc.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))).and
        (((nearRegularExceptionCoefficient_tends_to_zero A B).eventually
          (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))).and
          (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))))))
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd k Δ a loss s hΔ hdegree hmin hmax hloss hseed
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right _ _).trans hd)
  obtain ⟨hm, hc, hsmall, hlog⟩ := hx₀ d hx
  have hL : 0 < Real.log (d : ℝ) := by linarith
  have hmatch : 2 * A * (Real.log d) ^ nearRegularDegreePower ≤ (Real.log d) ^ (1 / 16 : ℝ) := by
    apply (div_le_one (Real.rpow_pos_of_pos hL _)).mp
    simpa only [mul_div_assoc, ← Real.rpow_sub hL] using hm.le
  have hcost : 8 * A * (Real.log d) ^ nearRegularDegreePower ≤ (Real.log d) ^ (1 / 4 : ℝ) := by
    apply (div_le_one (Real.rpow_pos_of_pos hL _)).mp
    simpa only [mul_div_assoc, ← Real.rpow_sub hL] using hc.le
  exact near_regular_certificate_budgets A B d k Δ a loss s hB hdR hlog hΔ hdegree hmin hmax
    hloss hseed hmatch hcost hsmall.le

end Erdos911
