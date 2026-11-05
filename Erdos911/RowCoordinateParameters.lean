import Erdos911.DictionaryParameters

namespace Erdos911

noncomputable def dictionaryRowThreshold (q B : ℕ) : ℕ :=
  Nat.ceil ((B : ℝ) / (8 * dictionaryLeftSize q))

noncomputable def dictionaryRowEventWeight (q B : ℕ) : ℝ :=
  Real.exp (-(q : ℝ) * B / (1024 * dictionaryLeftSize q))

noncomputable def dictionaryRowWeightBudget (q : ℕ) : ℝ :=
  (q : ℝ) / (8192 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q)

noncomputable def dictionaryRowEventCount (q : ℕ) : ℕ :=
  dictionaryLowDegree q * ((dictionaryLeftSize q + 1) * dictionaryConflictDegree q ^ (2 * dictionaryLeftSize q)) *
    (16 * dictionaryPatternCount q * dictionaryDegreeCharge q) *
      ((dictionaryBadLimit q + 1) * dictionaryWordLength q ^ dictionaryBadLimit q)

theorem dictionaryWordLength_pos (q : ℕ) : 0 < dictionaryWordLength q := by
  have h := Nat.le_ceil (Real.exp (Real.log 2 * q / 16))
  have hp := Real.exp_pos (Real.log 2 * q / 16)
  have hh : (0 : ℝ) < dictionaryWordLength q := hp.trans_le h
  exact_mod_cast hh

instance (q : ℕ) : NeZero (dictionaryWordLength q) := ⟨(dictionaryWordLength_pos q).ne'⟩

theorem dictionaryRowThreshold_pos (q B : ℕ) (hq : 0 < q) (hB : 0 < B) :
    0 < dictionaryRowThreshold q B := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hp : (0 : ℝ) < (B : ℝ) / (8 * dictionaryLeftSize q) := by
    unfold dictionaryLeftSize
    positivity
  have h := Nat.le_ceil ((B : ℝ) / (8 * dictionaryLeftSize q))
  have hh : (0 : ℝ) < dictionaryRowThreshold q B := hp.trans_le h
  exact_mod_cast hh

theorem dictionaryRowThreshold_lower (q B : ℕ) :
    (B : ℝ) / (8 * dictionaryLeftSize q) ≤ dictionaryRowThreshold q B := Nat.le_ceil _

end Erdos911
