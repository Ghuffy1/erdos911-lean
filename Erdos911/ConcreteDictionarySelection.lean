import Erdos911.DictionaryFailureBudget

namespace Erdos911

/-- The number of all partial label maps on a small left set is bounded
by the test count used in the dictionary probability estimate. -/
theorem dictionary_partial_map_count (q : ℕ) (A : Type*) [Fintype A] [DecidableEq A]
    (hA : Fintype.card A ≤ dictionaryLeftSize q) :
    Fintype.card (A → Option (Fin (dictionaryLabelCount q))) ≤ dictionaryTestCount q := by
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  exact Nat.pow_le_pow_right (Nat.succ_pos _) hA

/-- The dictionary-selection probability bound is completely discharged
for q>=65536. Good blocks carry at least seven eighths of the chosen mass. -/
theorem exists_concrete_dictionary {R I : Type*} [DecidableEq R] [Fintype I]
    (q : ℕ) (hq : 65536 ≤ q) (T : I → Type*) [∀ i, Fintype (T i)]
    (N : ∀ i, T i → R → Finset (Fin (dictionaryLabelCount q)))
    (U : ∀ i, T i → Finset R)
    (hmin : ∀ i t y, y ∈ U i t → dictionaryRowMinimum q ≤ (N i t y).card)
    (hcount : ∀ i, Fintype.card (T i) ≤ dictionaryTestCount q)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool,
      (7 / 8 : ℝ) * (∑ i : I, w i) ≤
        ∑ i : I, if (∀ t : T i,
          (eventHitSet (dictionaryBadCoordinate (N i t) (U i t)) Finset.univ ω).card < dictionaryBadLimit q)
          then w i else 0 := by
  have hbudget : (dictionaryTestCount q : ℝ) *
      (8 * (Fintype.card (Fin (dictionaryWordLength q)) : ℝ) ^ 2 *
        (1 / 2 : ℝ) ^ dictionaryRowMinimum q) ^ dictionaryBadLimit q ≤ 1 / 8 := by
    simpa only [Fintype.card_fin] using dictionary_failure_budget q hq
  obtain ⟨ω, hω⟩ := exists_dictionary_good_mass
    (L := Fin (dictionaryLabelCount q)) (C := Fin (dictionaryWordLength q)) (R := R) (I := I)
    T N U (dictionaryRowMinimum q)
    (dictionaryBadLimit q) (dictionaryTestCount q) (1 / 8) hmin hcount
    hbudget w hw
  refine ⟨ω, ?_⟩
  rw [show (1 : ℝ) - 1 / 8 = 7 / 8 by norm_num] at hω
  exact hω

end Erdos911
