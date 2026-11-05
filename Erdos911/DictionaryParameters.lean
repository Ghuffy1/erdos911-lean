import Erdos911.DictionarySelection
import Erdos911.ConnectedSetLabels

namespace Erdos911

def dictionaryLeftSize (q : ℕ) : ℕ := q ^ 20
def dictionaryDegreeCharge (q : ℕ) : ℕ := q ^ 50
def dictionaryLowDegree (q : ℕ) : ℕ := 8 * dictionaryDegreeCharge q
def dictionaryPatternCount (q : ℕ) : ℕ := (dictionaryLeftSize q + 1) ^ q
def dictionaryConflictDegree (q : ℕ) : ℕ :=
  16 * dictionaryPatternCount q * dictionaryDegreeCharge q * dictionaryLowDegree q
def dictionaryLabelCount (q : ℕ) : ℕ := (dictionaryConflictDegree q + 1) ^ dictionaryLeftSize q + 1
def dictionaryTestCount (q : ℕ) : ℕ := (dictionaryLabelCount q + 1) ^ dictionaryLeftSize q
def dictionaryBadLimit (q : ℕ) : ℕ := q ^ 43
def dictionaryRowMinimum (q : ℕ) : ℕ := q / 2
noncomputable def dictionaryWordLength (q : ℕ) : ℕ := Nat.ceil (Real.exp (Real.log 2 * q / 16))

theorem dictionary_log_two_bounds : (1 / 2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h

end Erdos911
