import Erdos911.NearRegularCertificateEstimates
import Erdos911.StarPruningBounds
import Erdos911.RepeatedTypeParameters

namespace Erdos911

theorem near_regular_available_log_upper (A M : ℝ) (d k a D Δ : ℕ)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hd : 1 ≤ d) (hk : d ≤ k) (ha : 0 < a) (hD : 0 < D)
    (hlog : 0 < Real.log d) (haverage : (d : ℝ) * k ≤ 2 * a)
    (hdegree : (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower)
    (hupper : (D : ℝ) ≤ 32 * M * d * Δ) :
    Real.log (((D * k : ℕ) : ℝ) / a) ≤
      Real.log d + nearRegularDegreePower * Real.log (Real.log d) + Real.log (64 * M * A) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hApos : 0 < A := by linarith
  have hMpos : 0 < M := by linarith
  have hratio : ((D * k : ℕ) : ℝ) / a ≤ 64 * M * Δ := by
    apply (div_le_iff₀ haR).mpr
    have hDk := mul_le_mul_of_nonneg_right hupper hkR.le
    have he := mul_le_mul_of_nonneg_left haverage (show 0 ≤ 32 * M * (Δ : ℝ) by positivity)
    push_cast
    nlinarith only [hDk, he]
  have htarget : ((D * k : ℕ) : ℝ) / a ≤
      (64 * M * A) * d * (Real.log d) ^ nearRegularDegreePower := by
    apply hratio.trans
    have h := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 64 * M by positivity)
    nlinarith only [h]
  have hpositive : 0 < ((D * k : ℕ) : ℝ) / a := by
    rw [Nat.cast_mul]
    exact div_pos (mul_pos hDR hkR) haR
  apply (Real.log_le_log hpositive htarget).trans_eq
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hlog _).ne',
    Real.log_mul (by positivity) hdR.ne', Real.log_rpow hlog]
  ring

theorem near_regular_pair_log_lower (M : ℝ) (d k a D Δ : ℕ)
    (hM : 1 ≤ M) (hd : 1 ≤ d) (hk : d ≤ k) (ha : 0 < a)
    (hupper : 2 * (a : ℝ) ≤ (Δ : ℝ) * k)
    (hlower : 16 * M * d * Δ ≤ (D : ℝ)) :
    (1 / 2 : ℝ) * Real.log d ≤
      Real.log (((D * k : ℕ) : ℝ) /
        ((a : ℝ) * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hMpos : 0 < M := by linarith
  have hqpos : 0 < nearRegularBlockSize d := by have h := (nearRegularBlockSize_bounds d hd).1; omega
  have hq := (nearRegularBlockSize_bounds d hd).2.2
  have hq2 : ((nearRegularBlockSize d * nearRegularBlockSize d : ℕ) : ℝ) ≤ 4 * (d : ℝ) ^ (1 / 2 : ℝ) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (nearRegularBlockSize d)) hq 2
    rw [mul_pow, ← Real.rpow_mul_natCast hdR.le] at h
    norm_num at h
    simpa only [Nat.cast_mul, pow_two] using h
  have havailable : 32 * M * d ≤ ((D * k : ℕ) : ℝ) / a := by
    apply (le_div_iff₀ haR).mpr
    have hDk := mul_le_mul_of_nonneg_right hlower hkR.le
    have he := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 16 * M * d by positivity)
    push_cast
    nlinarith only [hDk, he]
  have hsquare : ((d : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = d := by
    rw [← Real.rpow_mul_natCast hdR.le]
    norm_num
  have hroot : (d : ℝ) ^ (1 / 2 : ℝ) ≤
      (((D * k : ℕ) : ℝ) / a) / (nearRegularBlockSize d * nearRegularBlockSize d : ℕ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hscaled := mul_le_mul_of_nonneg_left hq2 (Real.rpow_nonneg hdR.le (1 / 2 : ℝ))
    have hdM := mul_le_mul_of_nonneg_right hM hdR.le
    nlinarith only [hscaled, hsquare, hdM, havailable]
  have heq : (((D * k : ℕ) : ℝ) / a) / (nearRegularBlockSize d * nearRegularBlockSize d : ℕ) =
      ((D * k : ℕ) : ℝ) / ((a : ℝ) * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ)) := by ring
  rw [heq] at hroot
  have h := Real.log_le_log (Real.rpow_pos_of_pos hdR (1 / 2 : ℝ)) hroot
  simpa only [Real.log_rpow hdR] using h

theorem tolerantTupleOrder_le_log (d : ℝ) (hlog : 1 ≤ Real.log d) :
    (tolerantTupleOrder d : ℝ) ≤ Real.log d := by
  have hfloor : (tolerantTupleOrder d : ℝ) ≤ Real.sqrt (Real.log d) / 20 := Nat.floor_le (by positivity)
  have hsqrt : (Real.sqrt (Real.log d)) ^ 2 = Real.log d := Real.sq_sqrt (by linarith)
  have hn := Real.sqrt_nonneg (Real.log d)
  nlinarith

noncomputable def nearRegularTypeError (d : ℝ) : ℝ := 64 * (Real.log d) ^ 2 / d

theorem near_regular_star_overhead (d k a D : ℕ)
    (hd : 1 ≤ d) (hD : 1 ≤ D) (hDpow : D ≤ d ^ 3) (hlog : 1 ≤ Real.log d)
    (haverage : (d : ℝ) * k ≤ 2 * a) :
    ((2 * (k - 1) : ℕ) : ℝ) * Real.log D +
      ((tolerantTupleOrder d * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) +
      (k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ) ≤ (a : ℝ) * nearRegularTypeError d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogD : Real.log D ≤ 3 * Real.log d := by
    apply (Real.log_le_log hDR (show (D : ℝ) ≤ (d : ℝ) ^ 3 by exact_mod_cast hDpow)).trans_eq
    rw [Real.log_pow]
    norm_num
  have hD2 : D ^ 2 ≤ d ^ 6 := by
    have h := Nat.pow_le_pow_left hDpow 2
    simpa only [← pow_mul] using h
  have hlogD2 : Real.log ((D ^ 2 + 1 : ℕ) : ℝ) ≤ 6 * Real.log d + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat] using
      log_polynomial_successor_le 6 d (D ^ 2) (one_le_pow₀ hD) hD2
  have hlogD1 : Real.log ((D + 1 : ℕ) : ℝ) ≤ 3 * Real.log d + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using log_polynomial_successor_le 3 d D hD hDpow
  have hroot : ((2 * (k - 1) : ℕ) : ℝ) * Real.log D ≤ 6 * k * Real.log d := by
    have hn : ((2 * (k - 1) : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (show 2 * (k - 1) ≤ 2 * k by omega)
    have hl : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
    exact (mul_le_mul_of_nonneg_right hn hl).trans (by nlinarith [mul_le_mul_of_nonneg_left hlogD (show 0 ≤ 2 * (k : ℝ) by positivity)])
  have htuple : ((tolerantTupleOrder d * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) ≤
      (Real.log d) * k * (6 * Real.log d + 1) := by
    have hs := mul_le_mul_of_nonneg_right (tolerantTupleOrder_le_log d hlog) (Nat.cast_nonneg (α := ℝ) k)
    have h1 := mul_le_mul_of_nonneg_left hlogD2 (show 0 ≤ ((tolerantTupleOrder d * k : ℕ) : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 6 * Real.log d + 1 by linarith)
    push_cast at h1 ⊢
    nlinarith only [h1, h2]
  have hlast := mul_le_mul_of_nonneg_left hlogD1 (Nat.cast_nonneg (α := ℝ) k)
  have hsum : ((2 * (k - 1) : ℕ) : ℝ) * Real.log D +
      ((tolerantTupleOrder d * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) +
      (k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ) ≤ 32 * k * (Real.log d) ^ 2 := by
    have hL2 : Real.log d ≤ (Real.log d) ^ 2 := by nlinarith
    have hk := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hL2)
    have hk1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hlog)
    nlinarith only [hroot, htuple, hlast, hk, hk1]
  apply hsum.trans
  unfold nearRegularTypeError
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hdR).mpr
  have h := mul_le_mul_of_nonneg_right haverage (show 0 ≤ 32 * (Real.log d) ^ 2 by positivity)
  nlinarith only [h]

end Erdos911
