import Erdos911.BlockPairWitness
import Erdos911.PairSubsetCounting

namespace Erdos911

noncomputable def repeatedBlockSubsets {V : Type*} [DecidableEq V]
    (P : Finset (RectangleBlock V)) (T : Finset (Sym2 V)) (a j : ℕ) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (T.powersetCard a).filter (fun F => 3 * j ≤ repeatedEdgeVolume P F)

theorem mem_repeatedBlockSubsets {V : Type*} [DecidableEq V]
    (P : Finset (RectangleBlock V)) (T F : Finset (Sym2 V)) (a j : ℕ) :
    F ∈ repeatedBlockSubsets P T a j ↔
      F ⊆ T ∧ F.card = a ∧ 3 * j ≤ repeatedEdgeVolume P F := by
  classical
  simp only [repeatedBlockSubsets, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

theorem repeatedBlockSubsets_subset_pairWitnessSubsets_of_disjoint {V : Type*} [DecidableEq V]
    (P : Finset (RectangleBlock V))
    (hP : (P : Set (RectangleBlock V)).PairwiseDisjoint RectangleBlock.edges)
    (T : Finset (Sym2 V)) (a j : ℕ) :
    repeatedBlockSubsets P T a j ⊆ pairWitnessSubsets T (sameBlockPairs P T) a j := by
  classical
  intro F hF
  obtain ⟨hFset, hrepeat⟩ := Finset.mem_filter.mp hF
  obtain ⟨hFT, hFcard⟩ := Finset.mem_powersetCard.mp hFset
  obtain ⟨Q, hQ, hQP, hQcard⟩ := exists_repeated_edge_pairs_of_disjoint P hP F j hrepeat
  exact (mem_pairWitnessSubsets T (sameBlockPairs P T) a j F).mpr
    ⟨hFT, hFcard, Q, hQ, hQP.trans (sameBlockPairs_mono P hFT), hQcard⟩

theorem repeatedBlockSubsets_subset_pairWitnessSubsets {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (T : Finset (Sym2 V)) (a j : ℕ) :
    repeatedBlockSubsets P T a j ⊆ pairWitnessSubsets T (sameBlockPairs P T) a j :=
  repeatedBlockSubsets_subset_pairWitnessSubsets_of_disjoint P hP.2 T a j

theorem repeatedBlockSubsets_card_le_of_bounded {V : Type*} [DecidableEq V]
    {P : Finset (RectangleBlock V)} {M : ℕ} (hP : BoundedEdgeBlocks P M)
    (T : Finset (Sym2 V)) (a j : ℕ) :
    (repeatedBlockSubsets P T a j).card ≤
      (T.card * M).choose j * T.card.choose (a - 2 * j) := by
  calc
    (repeatedBlockSubsets P T a j).card ≤
        (pairWitnessSubsets T (sameBlockPairs P T) a j).card :=
      Finset.card_le_card (repeatedBlockSubsets_subset_pairWitnessSubsets_of_disjoint P hP.2 T a j)
    _ ≤ (sameBlockPairs P T).card.choose j * T.card.choose (a - 2 * j) :=
      pairWitnessSubsets_card_le T (sameBlockPairs P T) a j
    _ ≤ (T.card * M).choose j * T.card.choose (a - 2 * j) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_choose j (sameBlockPairs_card_le_of_bounded hP T))

/-- The finite repeated-block count, before the logarithmic estimates.
It counts all available edge subsets, including those that are not graph copies. -/
theorem repeatedBlockSubsets_card_le {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (T : Finset (Sym2 V)) (a j : ℕ) :
    (repeatedBlockSubsets P T a j).card ≤
    (T.card * (q * q)).choose j * T.card.choose (a - 2 * j) :=
  repeatedBlockSubsets_card_le_of_bounded hP.boundedEdgeBlocks T a j

end Erdos911
