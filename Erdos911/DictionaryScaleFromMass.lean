import Erdos911.DictionaryScales
import Erdos911.RowCoordinateParameters
import Mathlib.Data.Nat.Log

namespace Erdos911

theorem dictionary_scale_from_mass {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q b : ℕ) (hq : 0 < q)
    (hb : 128 * q ^ 69 ≤ b) (W : Finset V)
    (hmin : ∀ x ∈ W, b ≤ 8 * dictionaryPatternCount q * K.degree x)
    (hmax : ∀ x ∈ W, K.degree x ≤ dictionaryDegreeCharge q * b) :
    AdmissibleDictionaryScale K q W (Nat.log 2 b) := by
  have hbpos : 0 < b := (by positivity : 0 < 128 * q ^ 69).trans_le hb
  have hlo : 2 ^ Nat.log 2 b ≤ b := Nat.pow_log_le_self 2 hbpos.ne'
  have hhi : b < 2 * 2 ^ Nat.log 2 b := by
    simpa only [pow_succ, mul_comm] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b
  refine ⟨?_, fun x hx => hlo.trans (hmin x hx), ?_⟩
  · have heq : 16 * dictionaryLeftSize q * dictionaryLowDegree q = q * (128 * q ^ 69) := by
      unfold dictionaryLeftSize dictionaryLowDegree dictionaryDegreeCharge
      ring
    have hprod := Nat.mul_le_mul_left q hb
    have hprod' := Nat.mul_lt_mul_of_pos_left hhi hq
    have hfinal : 2 * (8 * dictionaryLeftSize q * dictionaryLowDegree q) <
        2 * (q * 2 ^ Nat.log 2 b) := by nlinarith only [heq, hprod, hprod']
    omega
  · intro x hx
    have hΓ : 0 < dictionaryDegreeCharge q := by unfold dictionaryDegreeCharge; positivity
    have hh := Nat.mul_lt_mul_of_pos_left hhi hΓ
    have := hmax x hx
    nlinarith only [hh, this]

theorem dictionary_threshold_le_of_mass (q B n : ℕ) (hq : 0 < q)
    (h : B ≤ 8 * dictionaryLeftSize q * n) : dictionaryRowThreshold q B ≤ n := by
  unfold dictionaryRowThreshold
  apply Nat.ceil_le.mpr
  have ha : (0 : ℝ) < 8 * dictionaryLeftSize q := by unfold dictionaryLeftSize; positivity
  apply (div_le_iff₀ ha).mpr
  exact_mod_cast h.trans_eq (by ring)

end Erdos911
