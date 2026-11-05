import Erdos911.SeedResidualColoring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos911

theorem log_order_uniform_bound (d k : ℝ) (hd : 1 ≤ d) (hdk : d ≤ k) :
    Real.log k ≤ (k / d) * (Real.log d + 1) := by
  have hdpos : 0 < d := by linarith
  have hkpos : 0 < k := hdpos.trans_le hdk
  have hratio : 1 ≤ k / d := (one_le_div hdpos).mpr hdk
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hkpos hdpos)
  have hsplit : Real.log k = Real.log d + Real.log (k / d) := by
    rw [Real.log_div hkpos.ne' hdpos.ne']
    ring
  have hscale := mul_le_mul_of_nonneg_right hratio hlogd
  rw [hsplit]
  nlinarith

theorem log_successor_order_uniform_bound (d k : ℝ) (hd : 1 ≤ d) (hdk : d ≤ k) :
    Real.log (k + 1) ≤ (k / d) * (Real.log d + 2) := by
  have hdpos : 0 < d := by linarith
  have hk : 1 ≤ k := hd.trans hdk
  have hkpos : 0 < k := by linarith
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hratio : 1 ≤ k / d := (one_le_div hdpos).mpr hdk
  have hlogk := log_order_uniform_bound d k hd hdk
  calc
    Real.log (k + 1) ≤ Real.log (2 * k) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log k := Real.log_mul (by norm_num) hkpos.ne'
    _ ≤ (k / d) * (Real.log d + 2) := by nlinarith

theorem log_seedAssignmentCountBound (k D s q : ℕ) (hk : 0 < k) (hD : 0 < D) :
    Real.log (seedAssignmentCountBound k D D s q : ℝ) =
      Real.log k + Real.log ((D : ℝ) + 1) + Real.log ((s : ℝ) + 1) +
        (s : ℝ) * (4 * Real.log D + Real.log 2) + (k : ℝ) * Real.log ((q : ℝ) + 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  simp only [seedAssignmentCountBound, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, Nat.cast_ofNat]
  repeat rw [Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

theorem log_polynomial_successor_le (A d D : ℕ) (hD : 1 ≤ D)
    (hDpow : D ≤ d ^ A) :
    Real.log ((D : ℝ) + 1) ≤ (A : ℝ) * Real.log d + 1 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlogD : Real.log D ≤ (A : ℝ) * Real.log d := by
    calc
      Real.log D ≤ Real.log ((d : ℝ) ^ A) := Real.log_le_log hDpos (by exact_mod_cast hDpow)
      _ = _ := Real.log_pow ..
  have htwo := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at htwo
  calc
    Real.log ((D : ℝ) + 1) ≤ Real.log (2 * (D : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 2 + Real.log D := Real.log_mul (by norm_num) hDpos.ne'
    _ ≤ _ := by linarith

/-- The seed-order contribution is bounded uniformly in the component
order once its size is a fixed multiple of `k*log(d)/d`. -/
theorem uniform_seed_assignment_log_bound_of_log_choices (A d k D s q : ℕ) (C b : ℝ)
    (hd : 1 ≤ d) (hdk : d ≤ k) (hD : 1 ≤ D) (hDpow : D ≤ d ^ A)
    (hs : s ≤ k)
    (hseed : (s : ℝ) ≤ C * k * Real.log d / d)
    (hq : Real.log ((q : ℝ) + 1) ≤ b) :
    Real.log (seedAssignmentCountBound k D D s q : ℝ) ≤
      (k : ℝ) * (b +
        (((A : ℝ) + 2) * Real.log d + 4 +
          C * Real.log d * (4 * A * Real.log d + 1)) / d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hdk
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hdkreal : (d : ℝ) ≤ k := by exact_mod_cast hdk
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hdreal
  have hratio : 1 ≤ (k : ℝ) / d := (one_le_div hdpos).mpr hdkreal
  have hlogD : Real.log D ≤ (A : ℝ) * Real.log d := by
    calc
      Real.log D ≤ Real.log ((d : ℝ) ^ A) :=
        Real.log_le_log hDpos (by exact_mod_cast hDpow)
      _ = (A : ℝ) * Real.log d := Real.log_pow ..
  have hlogDplus : Real.log ((D : ℝ) + 1) ≤
      ((k : ℝ) / d) * ((A : ℝ) * Real.log d + 1) := by
    have hbound := log_polynomial_successor_le A d D hD hDpow
    exact hbound.trans (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) A) hlogd])
  have hlogk := log_order_uniform_bound (d : ℝ) k hdreal hdkreal
  have hlogs : Real.log ((s : ℝ) + 1) ≤ ((k : ℝ) / d) * (Real.log d + 2) := by
    have hsk : (s : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hs 1
    apply (Real.log_le_log (by positivity) hsk).trans
    exact log_successor_order_uniform_bound (d : ℝ) k hdreal hdkreal
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hdegree : (s : ℝ) * (4 * Real.log D + Real.log 2) ≤
      (C * k * Real.log d / d) * (4 * A * Real.log d + 1) := by
    apply (mul_le_mul_of_nonneg_left (show 4 * Real.log D + Real.log 2 ≤
      4 * A * Real.log d + 1 by linarith) (Nat.cast_nonneg s)).trans
    exact mul_le_mul_of_nonneg_right hseed (by positivity)
  have hchoices := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg (α := ℝ) k)
  rw [log_seedAssignmentCountBound k D s q hkpos (by omega)]
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add hlogk hlogDplus) hlogs) hdegree) hchoices
  apply hsum.trans_eq
  field_simp
  ring

theorem uniform_seed_assignment_log_bound (A d k D s q : ℕ) (C : ℝ)
    (hd : 1 ≤ d) (hdk : d ≤ k) (hD : 1 ≤ D) (hDpow : D ≤ d ^ A)
    (hs : s ≤ k)
    (hseed : (s : ℝ) ≤ C * k * Real.log d / d)
    (hq : Real.log ((q : ℝ) + 1) ≤ 6 * Real.log (Real.log d)) :
    Real.log (seedAssignmentCountBound k D D s q : ℝ) ≤
      (k : ℝ) * (6 * Real.log (Real.log d) +
        (((A : ℝ) + 2) * Real.log d + 4 +
          C * Real.log d * (4 * A * Real.log d + 1)) / d) := by
  exact uniform_seed_assignment_log_bound_of_log_choices A d k D s q C
    (6 * Real.log (Real.log d)) hd hdk hD hDpow hs hseed hq

end Erdos911
