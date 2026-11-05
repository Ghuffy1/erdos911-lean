import Erdos911.PairBandHostDegrees
import Erdos911.PairMarkingParameters

namespace Erdos911

noncomputable def lightHostLeftCutoff (d : ℕ) (M P : ℝ) : ℕ := Nat.ceil (16 * M * (d : ℝ) ^ 5 * P)
noncomputable def lightHostRightCutoff (d : ℕ) (M : ℝ) : ℕ := Nat.ceil (16 * M * (d : ℝ) ^ 2)
noncomputable def lightPairBaseDegree (d : ℕ) (M P : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (2 * (lightHostLeftCutoff d M P : ℝ) * lightHostRightCutoff d M / (2 : ℝ) ^ n) + 2

theorem light_host_cutoff_bounds (d : ℕ) (M P : ℝ)
    (hd : 65536 ≤ d) (hM : 1 ≤ M) (hM2 : M ^ 2 ≤ d) (hP : (d : ℝ) ^ 200 ≤ P) :
    16 * M * (d : ℝ) ^ 5 * P ≤ (lightHostLeftCutoff d M P : ℝ) ∧
      (lightHostLeftCutoff d M P : ℝ) ≤ 32 * M * (d : ℝ) ^ 5 * P ∧
      16 * M * (d : ℝ) ^ 2 ≤ (lightHostRightCutoff d M : ℝ) ∧
      (lightHostRightCutoff d M : ℝ) ≤ 32 * M * (d : ℝ) ^ 2 ∧
      (lightHostRightCutoff d M : ℝ) ^ 2 ≤ 1024 * (d : ℝ) ^ 5 ∧
      (lightHostLeftCutoff d M P : ℝ) * lightHostRightCutoff d M ≤ 1024 * (d : ℝ) ^ 8 * P ∧
      (lightHostRightCutoff d M : ℝ) < P := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd64 : (64 : ℝ) ≤ d := by exact_mod_cast (show 64 ≤ d by omega)
  have hdp : (0 : ℝ) < d := by linarith
  have hP1 : 1 ≤ P := (one_le_pow₀ hd1).trans hP
  have hM0 : 0 ≤ M := by linarith
  have hp0 : 0 ≤ P := by linarith
  have hx : 1 ≤ 16 * M * (d : ℝ) ^ 5 * P := by
    have hh := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hd1 : 1 ≤ (d : ℝ) ^ 5)) hP1
    nlinarith only [hh]
  have hy : 1 ≤ 16 * M * (d : ℝ) ^ 2 := by
    have hh := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hd1 : 1 ≤ (d : ℝ) ^ 2)
    nlinarith only [hh]
  have hDLlo : 16 * M * (d : ℝ) ^ 5 * P ≤ (lightHostLeftCutoff d M P : ℝ) := Nat.le_ceil _
  have hDRlo : 16 * M * (d : ℝ) ^ 2 ≤ (lightHostRightCutoff d M : ℝ) := Nat.le_ceil _
  have hDLhi : (lightHostLeftCutoff d M P : ℝ) ≤ 32 * M * (d : ℝ) ^ 5 * P := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ 16 * M * (d : ℝ) ^ 5 * P by positivity)).le
    change (lightHostLeftCutoff d M P : ℝ) ≤ _ at h
    nlinarith only [h, hx]
  have hDRhi : (lightHostRightCutoff d M : ℝ) ≤ 32 * M * (d : ℝ) ^ 2 := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ 16 * M * (d : ℝ) ^ 2 by positivity)).le
    change (lightHostRightCutoff d M : ℝ) ≤ _ at h
    nlinarith only [h, hy]
  have hsq : (lightHostRightCutoff d M : ℝ) ^ 2 ≤ 1024 * (d : ℝ) ^ 5 := by
    have h₁ := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) _) hDRhi 2
    have h₂ := mul_le_mul_of_nonneg_right hM2 (show 0 ≤ 1024 * (d : ℝ) ^ 4 by positivity)
    nlinarith only [h₁, h₂]
  have hprod : (lightHostLeftCutoff d M P : ℝ) * lightHostRightCutoff d M ≤ 1024 * (d : ℝ) ^ 8 * P := by
    have h₁ := mul_le_mul hDLhi hDRhi (Nat.cast_nonneg (α := ℝ) _) (by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hM2 (show 0 ≤ 1024 * (d : ℝ) ^ 7 * P by positivity)
    nlinarith only [h₁, h₂]
  have hMd : M ≤ (d : ℝ) := by nlinarith only [hM2, hM, hd1]
  have hlowpow : (d : ℝ) ^ 4 ≤ (d : ℝ) ^ 200 := pow_le_pow_right₀ hd1 (by norm_num)
  have hbig : 32 * M * (d : ℝ) ^ 2 < (d : ℝ) ^ 4 := by
    have h₁ := mul_le_mul_of_nonneg_right hMd (show 0 ≤ 32 * (d : ℝ) ^ 2 by positivity)
    have h₂ : 32 * (d : ℝ) ^ 3 < (d : ℝ) ^ 4 := by
      have hh := mul_lt_mul_of_pos_right (show (32 : ℝ) < d by linarith) (pow_pos hdp 3)
      nlinarith only [hh]
    nlinarith only [h₁, h₂]
  exact ⟨hDLlo, hDLhi, hDRlo, hDRhi, hsq, hprod, hDRhi.trans_lt (hbig.trans_le (hlowpow.trans hP))⟩

theorem light_pair_base_degree_bounds (d : ℕ) (M P : ℝ) (n : ℕ)
    (hd : 65536 ≤ d) (hM : 1 ≤ M) (hM2 : M ^ 2 ≤ d) (hP : (d : ℝ) ^ 200 ≤ P)
    (hbase : P / (d : ℝ) ^ 12 ≤ (2 : ℝ) ^ n) :
    2 ≤ lightPairBaseDegree d M P n ∧
      2 * (lightHostLeftCutoff d M P : ℝ) * lightHostRightCutoff d M ≤
        (lightPairBaseDegree d M P n : ℝ) * (2 : ℝ) ^ n ∧
      (lightPairBaseDegree d M P n : ℝ) ≤ 4096 * (d : ℝ) ^ 20 := by
  obtain ⟨_, _, _, _, _, hprod, _⟩ := light_host_cutoff_bounds d M P hd hM hM2 hP
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdp : (0 : ℝ) < d := by linarith
  have hPpos : 0 < P := (pow_pos hdp 200).trans_le hP
  have hbpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hPbase : P ≤ (2 : ℝ) ^ n * (d : ℝ) ^ 12 := (div_le_iff₀ (pow_pos hdp 12)).mp hbase
  have hratio : 2 * (lightHostLeftCutoff d M P : ℝ) * lightHostRightCutoff d M / (2 : ℝ) ^ n ≤
      2048 * (d : ℝ) ^ 20 := by
    apply (div_le_iff₀ hbpos).mpr
    have h₂ := mul_le_mul_of_nonneg_left hPbase (show 0 ≤ 2048 * (d : ℝ) ^ 8 by positivity)
    nlinarith only [hprod, h₂]
  have hlo := Nat.le_ceil (2 * (lightHostLeftCutoff d M P : ℝ) * lightHostRightCutoff d M / (2 : ℝ) ^ n)
  have hhi := (Nat.ceil_lt_add_one (show 0 ≤ 2 * (lightHostLeftCutoff d M P : ℝ) *
    lightHostRightCutoff d M / (2 : ℝ) ^ n by positivity)).le
  have hbig : 1 ≤ (d : ℝ) ^ 20 := one_le_pow₀ hd1
  refine ⟨by unfold lightPairBaseDegree; omega, ?_, ?_⟩
  · have hbound : 2 * (lightHostLeftCutoff d M P : ℝ) * lightHostRightCutoff d M /
        (2 : ℝ) ^ n ≤ (lightPairBaseDegree d M P n : ℝ) := by
      unfold lightPairBaseDegree
      push_cast
      linarith only [hlo]
    exact (div_le_iff₀ hbpos).mp hbound
  · unfold lightPairBaseDegree
    push_cast
    nlinarith only [hhi, hratio, hbig]

end Erdos911
