import Erdos911.NearRegularTypeRatios
import Erdos911.IncidenceTupleParameters

namespace Erdos911

noncomputable def incidenceTypeError (A : ℕ) (d : ℝ) : ℝ :=
  64 * ((A : ℝ) + 1) * (Real.log d) ^ 2 / d

theorem incidence_available_log_upper (M : ℝ) (d k e P : ℕ)
    (hM : 0 < M) (hd : 1 ≤ d) (hk : 0 < k) (he : 0 < e) (hP : 0 < P)
    (haverage : (d : ℝ) * k ≤ 2 * e) (hupper : (P : ℝ) ≤ 64 * M * (d : ℝ) ^ 2) :
    Real.log (((P * k : ℕ) : ℝ) / e) ≤ Real.log d + Real.log (128 * M) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hratio : ((P * k : ℕ) : ℝ) / e ≤ (128 * M) * d := by
    apply (div_le_iff₀ heR).mpr
    have hPk := mul_le_mul_of_nonneg_right hupper hkR.le
    have he' := mul_le_mul_of_nonneg_left haverage (show 0 ≤ 64 * M * d by positivity)
    push_cast
    nlinarith only [hPk, he']
  apply (Real.log_le_log (by rw [Nat.cast_mul]; positivity) hratio).trans_eq
  rw [Real.log_mul (by positivity) hdR.ne']
  ring

theorem incidence_pair_log_lower (M : ℝ) (d k e P : ℕ)
    (hM : 1 ≤ M) (hd : 1 ≤ d) (hk : d ≤ k) (he : 0 < e)
    (hupper : (e : ℝ) ≤ (d : ℝ) * k) (hlower : 32 * M * (d : ℝ) ^ 2 ≤ (P : ℝ)) :
    (1 / 2 : ℝ) * Real.log d ≤
      Real.log (((P * k : ℕ) : ℝ) /
        ((e : ℝ) * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ))) := by
  apply near_regular_pair_log_lower M d k e P (2 * d) hM hd hk he
  · push_cast
    linarith only [hupper]
  · push_cast
    nlinarith only [hlower]

theorem incidence_star_overhead (A d k e D : ℕ)
    (hd : 1 ≤ d) (hD : 1 ≤ D) (hDpow : D ≤ d ^ A) (hlog : 1 ≤ Real.log d)
    (haverage : (d : ℝ) * k ≤ 2 * e) :
    ((2 * (k - 1) : ℕ) : ℝ) * Real.log D +
      ((tolerantTupleOrder d * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) +
      (k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ) ≤ (e : ℝ) * incidenceTypeError A d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hlogD : Real.log D ≤ (A : ℝ) * Real.log d := by
    apply (Real.log_le_log hDR (show (D : ℝ) ≤ (d : ℝ) ^ A by exact_mod_cast hDpow)).trans_eq
    rw [Real.log_pow]
  have hD2 : D ^ 2 ≤ d ^ (2 * A) := by
    have h := Nat.pow_le_pow_left hDpow 2
    simpa only [← pow_mul, Nat.mul_comm] using h
  have hlogD2 : Real.log ((D ^ 2 + 1 : ℕ) : ℝ) ≤ 2 * A * Real.log d + 1 := by
    have h := log_polynomial_successor_le (2 * A) d (D ^ 2) (one_le_pow₀ hD) hD2
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using h
  have hlogD1 : Real.log ((D + 1 : ℕ) : ℝ) ≤ A * Real.log d + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using log_polynomial_successor_le A d D hD hDpow
  have hroot : ((2 * (k - 1) : ℕ) : ℝ) * Real.log D ≤ 2 * k * A * Real.log d := by
    have hn : ((2 * (k - 1) : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
      exact_mod_cast (show 2 * (k - 1) ≤ 2 * k by omega)
    have hl : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
    exact (mul_le_mul_of_nonneg_right hn hl).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hlogD (show 0 ≤ 2 * (k : ℝ) by positivity)])
  have htuple : ((tolerantTupleOrder d * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) ≤
      (Real.log d) * k * (2 * A * Real.log d + 1) := by
    have hs := mul_le_mul_of_nonneg_right (tolerantTupleOrder_le_log d hlog) (Nat.cast_nonneg (α := ℝ) k)
    have h1 := mul_le_mul_of_nonneg_left hlogD2 (show 0 ≤ ((tolerantTupleOrder d * k : ℕ) : ℝ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hs (show 0 ≤ 2 * (A : ℝ) * Real.log d + 1 by positivity)
    push_cast at h1 ⊢
    nlinarith only [h1, h2]
  have hlast := mul_le_mul_of_nonneg_left hlogD1 (Nat.cast_nonneg (α := ℝ) k)
  have hsum : ((2 * (k - 1) : ℕ) : ℝ) * Real.log D +
      ((tolerantTupleOrder d * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) +
      (k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ) ≤ 32 * ((A : ℝ) + 1) * k * (Real.log d) ^ 2 := by
    have hL2 : Real.log d ≤ (Real.log d) ^ 2 := by nlinarith
    have hk := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hL2)
    have hk1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hlog)
    have hkA := mul_nonneg hA hk
    nlinarith only [hroot, htuple, hlast, hk, hk1, hkA, hA,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sq_nonneg (Real.log d))]
  apply hsum.trans
  unfold incidenceTypeError
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hdR).mpr
  have h := mul_le_mul_of_nonneg_right haverage
    (show 0 ≤ 32 * ((A : ℝ) + 1) * (Real.log d) ^ 2 by positivity)
  nlinarith only [h]

end Erdos911
