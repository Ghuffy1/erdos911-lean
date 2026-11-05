import Erdos911.TwoScaleBlocks

namespace Erdos911

def BoundedEdgeBlocks {V : Type*} (P : Finset (RectangleBlock V)) (M : ℕ) : Prop :=
  (∀ B ∈ P, B.edges.card ≤ M) ∧ (P : Set (RectangleBlock V)).PairwiseDisjoint RectangleBlock.edges

theorem ValidBlockPacking.boundedEdgeBlocks {V : Type*} {G : SimpleGraph V}
    {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)} (hP : ValidBlockPacking G q ρ P) :
    BoundedEdgeBlocks P (q * q) := ⟨fun B hB => (hP.1 B hB).edges_card_le, hP.2⟩

theorem block_used_edges_sum_le_of_disjoint {V : Type*} [DecidableEq V]
    (P : Finset (RectangleBlock V))
    (hP : (P : Set (RectangleBlock V)).PairwiseDisjoint RectangleBlock.edges)
    (T : Finset (Sym2 V)) :
    ∑ B ∈ P, (B.edges ∩ T).card ≤ T.card := by
  classical
  have hdis : (P : Set (RectangleBlock V)).PairwiseDisjoint (fun B => B.edges ∩ T) := by
    intro B hB C hC hBC
    exact (hP hB hC hBC).mono Finset.inter_subset_left Finset.inter_subset_left
  have hsub : P.biUnion (fun B => B.edges ∩ T) ⊆ T := by
    intro e he
    obtain ⟨B, _, heB⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_inter.mp heB).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis] at hcard
  exact hcard

theorem block_used_edges_sum_le {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (T : Finset (Sym2 V)) :
    ∑ B ∈ P, (B.edges ∩ T).card ≤ T.card :=
  block_used_edges_sum_le_of_disjoint P hP.2 T

def sameBlockPairs {V : Type*} [DecidableEq V] (P : Finset (RectangleBlock V))
    (T : Finset (Sym2 V)) : Finset (Sym2 V × Sym2 V) :=
  P.biUnion (fun B => (B.edges ∩ T).offDiag)

theorem mem_sameBlockPairs {V : Type*} [DecidableEq V] (P : Finset (RectangleBlock V))
    (T : Finset (Sym2 V)) (a b : Sym2 V) :
    (a, b) ∈ sameBlockPairs P T ↔
      ∃ B ∈ P, a ∈ B.edges ∩ T ∧ b ∈ B.edges ∩ T ∧ a ≠ b := by
  classical
  simp only [sameBlockPairs, Finset.mem_biUnion, Finset.mem_offDiag]

theorem sameBlockPairs_mono {V : Type*} [DecidableEq V] (P : Finset (RectangleBlock V))
    {S T : Finset (Sym2 V)} (hST : S ⊆ T) : sameBlockPairs P S ⊆ sameBlockPairs P T := by
  rintro ⟨a, b⟩ h
  obtain ⟨B, hB, ha, hb, hab⟩ := (mem_sameBlockPairs P S a b).mp h
  exact (mem_sameBlockPairs P T a b).mpr
    ⟨B, hB, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1, hST (Finset.mem_inter.mp ha).2⟩,
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hb).1, hST (Finset.mem_inter.mp hb).2⟩, hab⟩

/-- Ordered pairs give a convenient upper bound for the unordered
same-block pairs used by the repeated-edge count. -/
theorem sameBlockPairs_card_le_of_bounded {V : Type*} [DecidableEq V]
    {P : Finset (RectangleBlock V)} {M : ℕ} (hP : BoundedEdgeBlocks P M)
    (T : Finset (Sym2 V)) :
    (sameBlockPairs P T).card ≤ T.card * M := by
  classical
  calc
    (sameBlockPairs P T).card ≤ ∑ B ∈ P, ((B.edges ∩ T).offDiag).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ B ∈ P, (B.edges ∩ T).card * M := by
      apply Finset.sum_le_sum
      intro B hB
      rw [Finset.offDiag_card]
      apply (Nat.sub_le _ _).trans
      apply Nat.mul_le_mul_left
      exact (Finset.card_le_card Finset.inter_subset_left).trans (hP.1 B hB)
    _ = (∑ B ∈ P, (B.edges ∩ T).card) * M := (Finset.sum_mul ..).symm
    _ ≤ T.card * M := Nat.mul_le_mul_right _ (block_used_edges_sum_le_of_disjoint P hP.2 T)

theorem sameBlockPairs_card_le {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (T : Finset (Sym2 V)) :
    (sameBlockPairs P T).card ≤ T.card * (q * q) :=
  sameBlockPairs_card_le_of_bounded hP.boundedEdgeBlocks T

def repeatedEdgeVolume {V : Type*} [DecidableEq V] (P : Finset (RectangleBlock V))
    (T : Finset (Sym2 V)) : ℕ :=
  ∑ B ∈ P, if 2 ≤ (B.edges ∩ T).card then (B.edges ∩ T).card else 0

def blockPairCount {V : Type*} [DecidableEq V] (P : Finset (RectangleBlock V))
    (T : Finset (Sym2 V)) : ℕ :=
  ∑ B ∈ P, (B.edges ∩ T).card / 2

theorem repeatedEdgeVolume_le_three_pairCount {V : Type*} [DecidableEq V]
    (P : Finset (RectangleBlock V)) (T : Finset (Sym2 V)) :
    repeatedEdgeVolume P T ≤ 3 * blockPairCount P T := by
  classical
  unfold repeatedEdgeVolume blockPairCount
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B _
  split_ifs <;> omega

end Erdos911
