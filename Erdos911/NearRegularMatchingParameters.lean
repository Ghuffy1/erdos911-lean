import Erdos911.NearRegularResidualParameters
import Erdos911.SeedEventParameters

open Filter

namespace Erdos911

noncomputable def nearRegularMatchingSize (d : ℝ) (k : ℕ) : ℕ :=
  Nat.floor ((k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ))

noncomputable def nearRegularExceptionBound (d : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) / (Real.log d) ^ (1 / 4 : ℝ)

theorem nearRegularMatchingSize_bounds (d : ℝ) (k : ℕ)
    (hlarge : 2 ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ)) :
    (k : ℝ) / (2 * (Real.log d) ^ (1 / 16 : ℝ)) ≤ nearRegularMatchingSize d k ∧
      (nearRegularMatchingSize d k : ℝ) ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ) := by
  have hfloor := Nat.lt_floor_add_one ((k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ))
  refine ⟨?_, Nat.floor_le (by positivity)⟩
  change _ ≤ (Nat.floor ((k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ)) : ℝ)
  have heq : (k : ℝ) / (2 * (Real.log d) ^ (1 / 16 : ℝ)) =
      ((k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ)) / 2 := by ring
  rw [heq]
  linarith

theorem near_regular_matching_mean (d : ℝ) (k : ℕ) (hlog : 0 < Real.log d)
    (hlarge : 2 ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ)) :
    (k : ℝ) / (2 * (Real.log d) ^ (3 / 16 : ℝ)) ≤
      nearRegularRoundSuccess d ^ 32 * nearRegularMatchingSize d k := by
  have hβ : 0 ≤ nearRegularRoundSuccess d ^ 32 := pow_nonneg (Real.rpow_nonneg hlog.le _) 32
  calc
    _ = nearRegularRoundSuccess d ^ 32 * ((k : ℝ) / (2 * (Real.log d) ^ (1 / 16 : ℝ))) := by
      rw [nearRegularRoundSuccess_pow d hlog]
      have hpower : (Real.log d) ^ (-1 / 8 : ℝ) / (Real.log d) ^ (1 / 16 : ℝ) =
          1 / (Real.log d) ^ (3 / 16 : ℝ) := by
        rw [← Real.rpow_sub hlog]
        norm_num
        rw [Real.rpow_neg hlog.le]
      calc
        _ = (k : ℝ) / 2 * (1 / (Real.log d) ^ (3 / 16 : ℝ)) := by ring
        _ = (k : ℝ) / 2 * ((Real.log d) ^ (-1 / 8 : ℝ) / (Real.log d) ^ (1 / 16 : ℝ)) := by rw [hpower]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (nearRegularMatchingSize_bounds d k hlarge).1 hβ

theorem near_regular_exception_mean_bound (d : ℝ) (k : ℕ) (hlog : 0 < Real.log d)
    (hlarge : 2 ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ))
    (hpower : 4 ≤ (Real.log d) ^ (1 / 16 : ℝ)) :
    nearRegularExceptionBound d k ≤ nearRegularRoundSuccess d ^ 32 * nearRegularMatchingSize d k / 2 := by
  have hden : 4 * (Real.log d) ^ (3 / 16 : ℝ) ≤ (Real.log d) ^ (1 / 4 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hlog.le (3 / 16 : ℝ))
    rw [← Real.rpow_add hlog] at h
    norm_num at h
    exact h
  calc
    _ ≤ (k : ℝ) / (4 * (Real.log d) ^ (3 / 16 : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by positivity) hden
    _ = ((k : ℝ) / (2 * (Real.log d) ^ (3 / 16 : ℝ))) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (near_regular_matching_mean d k hlog hlarge) (by norm_num)

theorem near_regular_matching_exponent_bound (d k : ℕ) (hd : 1 ≤ d)
    (hlog : 0 < Real.log d) (hlarge : 2 ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ))
    (hscale : 64 * (Real.log d) ^ (3 / 16 : ℝ) ≤ (d : ℝ) ^ (1 / 4 : ℝ)) :
    seedEventExponent d k ≤ nearRegularRoundSuccess d ^ 32 * nearRegularMatchingSize d k /
      (8 * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hqpos : 0 < nearRegularBlockSize d := by have h := (nearRegularBlockSize_bounds d hd).1; omega
  have hq := (nearRegularBlockSize_bounds d hd).2.2
  have hq2 : (nearRegularBlockSize d : ℝ) ^ 2 ≤ 4 * (d : ℝ) ^ (1 / 2 : ℝ) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (nearRegularBlockSize d)) hq 2
    rw [mul_pow, ← Real.rpow_mul_natCast hdR.le] at h
    norm_num at h
    exact h
  have hden : 16 * (nearRegularBlockSize d : ℝ) ^ 2 * (Real.log d) ^ (3 / 16 : ℝ) ≤
      (d : ℝ) ^ (3 / 4 : ℝ) := by
    calc
      _ ≤ 64 * (d : ℝ) ^ (1 / 2 : ℝ) * (Real.log d) ^ (3 / 16 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hq2 (Real.rpow_nonneg hlog.le (3 / 16 : ℝ))]
      _ ≤ (d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (1 / 4 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hdR.le (1 / 2 : ℝ))]
      _ = _ := by rw [← Real.rpow_add hdR]; norm_num
  calc
    _ ≤ (k : ℝ) / (16 * (nearRegularBlockSize d : ℝ) ^ 2 * (Real.log d) ^ (3 / 16 : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg k) (by positivity) hden
    _ = ((k : ℝ) / (2 * (Real.log d) ^ (3 / 16 : ℝ))) /
        (8 * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ)) := by push_cast; ring
    _ ≤ _ := div_le_div_of_nonneg_right (near_regular_matching_mean d k hlog hlarge) (by positivity)

theorem near_regular_matching_parameters_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k : ℕ, d ≤ k →
      nearRegularExceptionBound d k ≤ nearRegularRoundSuccess d ^ 32 * nearRegularMatchingSize d k / 2 ∧
      seedEventExponent d k ≤ nearRegularRoundSuccess d ^ 32 * nearRegularMatchingSize d k /
        (8 * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ)) := by
  have hratio : Tendsto (fun x : ℝ => (Real.log x) ^ (1 / 16 : ℝ) / x) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 / 16 : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  have hscale : Tendsto (fun x : ℝ => 64 * (Real.log x) ^ (3 / 16 : ℝ) / x ^ (1 / 4 : ℝ))
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      ((isLittleO_log_rpow_rpow_atTop (3 / 16 : ℝ)
        (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero).const_mul 64
  have hpower := ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 16 by norm_num)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop (4 : ℝ))
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((hratio.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).and
      ((hscale.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))).and (hpower.and hlogs)))
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd k hdk
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right _ _).trans hd)
  obtain ⟨hratio, hscale, hpower, hlog⟩ := hx₀ d hx
  have hlarge : 2 ≤ (k : ℝ) / (Real.log d) ^ (1 / 16 : ℝ) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog _)).mpr
    have h := (div_lt_iff₀ hdR).mp hratio
    have hk : (d : ℝ) ≤ k := by exact_mod_cast hdk
    linarith
  have hscale' : 64 * (Real.log d) ^ (3 / 16 : ℝ) ≤ (d : ℝ) ^ (1 / 4 : ℝ) := by
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hdR _)).mp hscale
    linarith
  exact ⟨near_regular_exception_mean_bound d k hlog hlarge hpower,
    near_regular_matching_exponent_bound d k hd1 hlog hlarge hscale'⟩

end Erdos911
