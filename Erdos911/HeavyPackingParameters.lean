import Erdos911.HeavyLargeRowPacking

namespace Erdos911

def heavyRowDegree (d : ℕ) : ℕ := d / 4
def heavyRightMinimum (d : ℕ) : ℕ := 128 * heavyRowDegree d ^ 69
def heavyCenterColors (d : ℕ) : ℕ := d ^ 17 * (d ^ 17 + 1) + 1

/-- Explicit polynomial parameter bounds for the large-block extraction. -/
theorem heavy_packing_parameters (d : ℕ) (hd : 2 ^ 32 ≤ d) :
    0 < heavyRowDegree d ∧ d ≤ 8 * heavyRowDegree d ∧
      heavyCenterColors d ≤ 4 * d ^ 34 ∧
      4 * heavyCenterColors d * heavyRightMinimum d * d ≤ d ^ 200 ∧
      d ^ 17 + 1 ≤ heavyRowDegree d ^ 20 := by
  have hd1 : 1 ≤ d := by norm_num at hd; omega
  have hq : 2 ^ 29 ≤ heavyRowDegree d := by unfold heavyRowDegree; norm_num at hd ⊢; omega
  have hq1 : 1 ≤ heavyRowDegree d := by norm_num at hq; omega
  have hdq : d ≤ 8 * heavyRowDegree d := by unfold heavyRowDegree; norm_num at hd; omega
  have hqle : heavyRowDegree d ≤ d := Nat.div_le_self _ _
  have hcolor : heavyCenterColors d ≤ 4 * d ^ 34 := by
    have hp : 1 ≤ d ^ 17 := Nat.one_le_pow _ _ hd1
    have heq : d ^ 34 = (d ^ 17) ^ 2 := by rw [← pow_mul]
    unfold heavyCenterColors
    nlinarith only [hp, heq]
  have hright : heavyRightMinimum d ≤ 128 * d ^ 69 := by
    exact Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hqle 69)
  have hd96 : 2048 ≤ d ^ 96 := by
    have hl : 2048 ≤ d := by norm_num at hd; omega
    exact hl.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hd1 (by norm_num : 1 ≤ 96))
  have hsmall : 4 * heavyCenterColors d * heavyRightMinimum d * d ≤ d ^ 200 := by
    calc
      _ ≤ 4 * (4 * d ^ 34) * (128 * d ^ 69) * d := by gcongr
      _ = 2048 * d ^ 104 := by ring
      _ ≤ d ^ 96 * d ^ 104 := Nat.mul_le_mul_right _ hd96
      _ = d ^ 200 := by rw [← pow_add]
  have hq3 : 2 * 8 ^ 17 ≤ heavyRowDegree d ^ 3 := by
    have hh := Nat.pow_le_pow_left hq 3
    norm_num at hh ⊢
    omega
  have hdpow : d ^ 17 ≤ 8 ^ 17 * heavyRowDegree d ^ 17 := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hdq 17
  have hqp : 1 ≤ heavyRowDegree d ^ 17 := Nat.one_le_pow _ _ hq1
  have hball : d ^ 17 + 1 ≤ heavyRowDegree d ^ 20 := by
    have hh := Nat.mul_le_mul_right (heavyRowDegree d ^ 17) hq3
    have heq : heavyRowDegree d ^ 20 = heavyRowDegree d ^ 3 * heavyRowDegree d ^ 17 := by rw [← pow_add]
    nlinarith only [hh, heq, hdpow, hqp]
  exact ⟨by omega, hdq, hcolor, hsmall, hball⟩

end Erdos911
