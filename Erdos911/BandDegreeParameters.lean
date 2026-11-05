import Erdos911.NearRegularCertificateEstimates

namespace Erdos911

def bandDegree (q : ℕ) : ℕ := q / 65536

noncomputable def bandLeftThreshold (q : ℕ) : ℝ :=
  (q : ℝ) * (Real.log q) ^ nearRegularDegreePower

noncomputable def bandLeftFloor (q : ℕ) : ℕ := Nat.floor (bandLeftThreshold q / 8)

theorem bandDegree_bounds (q : ℕ) (hq : 131072 ≤ q) :
    1 ≤ bandDegree q ∧ bandDegree q ≤ q ∧ q ≤ 131072 * bandDegree q ∧
      (1 / 262144 : ℝ) ≤ (bandDegree q : ℝ) / (2 * q) := by
  have hmod : q % 65536 < 65536 := Nat.mod_lt _ (by norm_num)
  have hdiv := Nat.mod_add_div q 65536
  have hd : 1 ≤ bandDegree q := by unfold bandDegree; omega
  have hupper : q ≤ 131072 * bandDegree q := by unfold bandDegree; omega
  refine ⟨hd, Nat.div_le_self q 65536, hupper, ?_⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply (le_div_iff₀ (show (0 : ℝ) < 2 * q by positivity)).mpr
  have hupperR : (q : ℝ) ≤ 131072 * bandDegree q := by exact_mod_cast hupper
  nlinarith only [hupperR]

theorem bandLeftFloor_lower (q : ℕ) (hq : 16 ≤ q) (hlog : 1 ≤ Real.log q) :
    bandLeftThreshold q / 16 ≤ (bandLeftFloor q : ℝ) := by
  have hpow : 1 ≤ (Real.log q) ^ nearRegularDegreePower :=
    Real.one_le_rpow hlog (by norm_num [nearRegularDegreePower])
  have hqR : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have hT : (16 : ℝ) ≤ bandLeftThreshold q := by
    unfold bandLeftThreshold
    nlinarith only [mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) q), hqR]
  have hf := Nat.lt_floor_add_one (bandLeftThreshold q / 8)
  change _ ≤ (Nat.floor (bandLeftThreshold q / 8) : ℝ)
  nlinarith only [hT, hf]

theorem band_normalization_mean_lower (q : ℕ) (hq : 131072 ≤ q) (hlog : 1 ≤ Real.log q) :
    (q : ℝ) / 4194304 ≤ (bandDegree q : ℝ) / (2 * q) * bandLeftFloor q := by
  have hprob := (bandDegree_bounds q hq).2.2.2
  have hfloor := bandLeftFloor_lower q (by omega) hlog
  have hpow : 1 ≤ (Real.log q) ^ nearRegularDegreePower :=
    Real.one_le_rpow hlog (by norm_num [nearRegularDegreePower])
  have hT : (q : ℝ) / 16 ≤ bandLeftThreshold q / 16 := by
    unfold bandLeftThreshold
    have h := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) q)
    nlinarith only [h]
  have hr : (q : ℝ) / 16 ≤ bandLeftFloor q := hT.trans hfloor
  have h := mul_le_mul hprob hr (by positivity : (0 : ℝ) ≤ q / 16)
    (by positivity : (0 : ℝ) ≤ (bandDegree q : ℝ) / (2 * q))
  nlinarith only [h]

theorem band_polynomial_degree_bound (B q a : ℕ)
    (hq : q ≤ 131072 * bandDegree q) (hd : 262144 ^ B ≤ bandDegree q)
    (ha : a ≤ (2 * q) ^ B) : a ≤ bandDegree q ^ (B + 1) := by
  have hq' : 2 * q ≤ 262144 * bandDegree q := by omega
  calc
    a ≤ (2 * q) ^ B := ha
    _ ≤ (262144 * bandDegree q) ^ B := Nat.pow_le_pow_left hq' B
    _ = 262144 ^ B * bandDegree q ^ B := Nat.mul_pow _ _ _
    _ ≤ bandDegree q * bandDegree q ^ B := Nat.mul_le_mul_right _ hd
    _ = bandDegree q ^ (B + 1) := by rw [pow_succ]; exact Nat.mul_comm _ _

end Erdos911
