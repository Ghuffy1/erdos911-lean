import Erdos911.TolerantSamplingParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace Erdos911

noncomputable def tupleContraction (x : ℝ) : ℝ := (Real.log x) ^ (-1 / 4 : ℝ)

theorem tolerantTupleOrder_lower (x : ℝ) (hlog : 6400 ≤ Real.log x) :
    2 ≤ tolerantTupleOrder x ∧
      Real.sqrt (Real.log x) / 40 ≤ ((tolerantTupleOrder x - 1 : ℕ) : ℝ) := by
  have hsqrt : (80 : ℝ) ≤ Real.sqrt (Real.log x) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    norm_num
    exact hlog
  have hr : 4 ≤ tolerantTupleOrder x := by
    apply Nat.le_floor
    norm_num
    linarith
  have hfloor := Nat.lt_floor_add_one (Real.sqrt (Real.log x) / 20)
  have hsub : ((tolerantTupleOrder x - 1 : ℕ) : ℝ) = (tolerantTupleOrder x : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  refine ⟨by omega, ?_⟩
  rw [hsub]
  change Real.sqrt (Real.log x) / 20 < (tolerantTupleOrder x : ℝ) + 1 at hfloor
  linarith

theorem tupleContraction_pos (x : ℝ) (hlog : 0 < Real.log x) : 0 < tupleContraction x :=
  Real.rpow_pos_of_pos hlog _

theorem tupleContraction_tends_to_zero : Tendsto tupleContraction atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => (Real.log x) ^ (-1 / 4 : ℝ)) atTop (nhds 0)
  simpa only [Function.comp_def, neg_div] using
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp Real.tendsto_log_atTop

theorem tupleContraction_sqrt (x : ℝ) (hlog : 0 < Real.log x) :
    tupleContraction x * Real.sqrt (Real.log x) = (Real.log x) ^ (1 / 4 : ℝ) := by
  unfold tupleContraction
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hlog]
  norm_num

theorem tuple_center_parameters_uniform (b : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D : ℝ, 0 < D →
      2 ≤ tolerantTupleOrder d ∧ 0 < tupleContraction d ∧ tupleContraction d ≤ 1 / 2 ∧
      Real.log (2 * D / (D / (Real.log d) ^ b)) /
        ((tolerantTupleOrder d - 1 : ℕ) : ℝ) ≤ tupleContraction d := by
  have hlogratio : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 4 : ℝ)) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
  have hconstant : Tendsto (fun x : ℝ => 1 / x ^ (1 / 4 : ℝ)) atTop (nhds 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num))
  have hlimit : Tendsto (fun x : ℝ => 40 * (Real.log 2 + b * Real.log x) / x ^ (1 / 4 : ℝ))
      atTop (nhds 0) := by
    have hsum := (hconstant.const_mul (40 * Real.log 2)).add (hlogratio.const_mul (40 * b))
    convert hsum using 1
    · funext x
      ring
    · simp
  have hsmall := (hlimit.comp Real.tendsto_log_atTop).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have htheta := tupleContraction_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (6400 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hsmall.and (htheta.and hlogs))
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd D hD
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hd)
  obtain ⟨hsmall, htheta, hlogs⟩ := hx₀ d hx
  have hL : 0 < Real.log (d : ℝ) := by linarith
  obtain ⟨hr, hlower⟩ := tolerantTupleOrder_lower d hlogs
  have hthetaPos := tupleContraction_pos d hL
  have hden : (0 : ℝ) < ((tolerantTupleOrder d - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < tolerantTupleOrder d - 1 by omega)
  have hratio : 2 * D / (D / (Real.log d) ^ b) = 2 * (Real.log d) ^ b := by
    have hp : (Real.log d) ^ b ≠ 0 := (Real.rpow_pos_of_pos hL b).ne'
    field_simp
  have hlogeq : Real.log (2 * D / (D / (Real.log d) ^ b)) =
      Real.log 2 + b * Real.log (Real.log d) := by
    rw [hratio, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hL b).ne', Real.log_rpow hL]
  have hnum : Real.log 2 + b * Real.log (Real.log d) ≤ (Real.log d) ^ (1 / 4 : ℝ) / 40 := by
    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hL (1 / 4 : ℝ))).mp hsmall
    linarith
  refine ⟨hr, hthetaPos, htheta.le, ?_⟩
  rw [hlogeq]
  apply (div_le_iff₀ hden).mpr
  have hscale := mul_le_mul_of_nonneg_left hlower hthetaPos.le
  rw [← mul_div_assoc, tupleContraction_sqrt d hL] at hscale
  exact hnum.trans hscale

theorem tupleContraction_power_log (x : ℝ) (hlog : 0 < Real.log x) :
    (tupleContraction x) ^ 31 * (Real.log x) ^ 4 = (Real.log x) ^ (-15 / 4 : ℝ) := by
  unfold tupleContraction
  rw [← Real.rpow_natCast _ 31, ← Real.rpow_mul hlog.le, ← Real.rpow_natCast _ 4,
    ← Real.rpow_add hlog]
  norm_num

theorem tuple_initial_contraction_uniform (t : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      ((t : ℝ) * tupleContraction d) ^ 31 * (baselineBlockSize d : ℝ) ≤ tolerantTupleOrder d := by
  have hlimit : Tendsto (fun x : ℝ => 2 * (t : ℝ) ^ 31 * (Real.log x) ^ (-15 / 4 : ℝ))
      atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_def, neg_div] using
      ((tendsto_rpow_neg_atTop (show (0 : ℝ) < 15 / 4 by norm_num)).comp Real.tendsto_log_atTop).const_mul
        (2 * (t : ℝ) ^ 31)
  have hsmall := hlimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (6400 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hsmall.and hlogs)
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hd)
  obtain ⟨hsmall, hlogs⟩ := hx₀ d hx
  have hL : 0 < Real.log (d : ℝ) := by linarith
  have htheta := tupleContraction_pos d hL
  have hLone : 1 ≤ Real.log (d : ℝ) := by linarith
  have hq : (baselineBlockSize d : ℝ) ≤ 2 * (Real.log d) ^ 4 := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (Real.log d) ^ 4 by positivity)).le
    have hpower := one_le_pow₀ hLone (n := 4)
    change (Nat.ceil ((Real.log d) ^ 4) : ℝ) ≤ _
    linarith
  have hbound : ((t : ℝ) * tupleContraction d) ^ 31 * (baselineBlockSize d : ℝ) ≤
      2 * (t : ℝ) ^ 31 * (Real.log d) ^ (-15 / 4 : ℝ) := by
    calc
      _ ≤ ((t : ℝ) * tupleContraction d) ^ 31 * (2 * (Real.log d) ^ 4) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 2 * (t : ℝ) ^ 31 * ((tupleContraction d) ^ 31 * (Real.log d) ^ 4) := by ring
      _ = _ := by rw [tupleContraction_power_log d hL]
  have hr := (tolerantTupleOrder_lower d hlogs).1
  have hrR : (1 : ℝ) ≤ tolerantTupleOrder d := by exact_mod_cast (show 1 ≤ tolerantTupleOrder d by omega)
  exact hbound.trans (hsmall.le.trans hrR)

end Erdos911
