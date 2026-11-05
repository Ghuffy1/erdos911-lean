import Erdos911.BlockPairCounting
import Erdos911.FinitePairing

namespace Erdos911

/-- The sum of the half-counts in the blocks is attained by mutually
endpoint-disjoint same-block pairs. -/
theorem exists_block_pair_packing_of_disjoint {V : Type*} [DecidableEq V]
    (P : Finset (RectangleBlock V))
    (hP : (P : Set (RectangleBlock V)).PairwiseDisjoint RectangleBlock.edges)
    (T : Finset (Sym2 V)) :
    ∃ Q : Finset (Sym2 V × Sym2 V), IsPairPacking T Q ∧
      Q ⊆ sameBlockPairs P T ∧ Q.card = blockPairCount P T := by
  classical
  choose pairs hpair hcard using (fun B : RectangleBlock V => exists_pair_packing (B.edges ∩ T))
  let Q := P.biUnion pairs
  have hsupport : ∀ B p, p ∈ pairs B → pairEndpoints p ⊆ B.edges := by
    intro B p hp
    exact (hpair B).endpoints_subset hp |>.trans Finset.inter_subset_left
  have hdis : (P : Set (RectangleBlock V)).PairwiseDisjoint pairs := by
    intro B hB C hC hBC
    apply Finset.disjoint_left.mpr
    intro p hpB hpC
    exact (Finset.disjoint_left.mp (hP hB hC hBC))
      ((Finset.mem_inter.mp ((hpair B).1 p hpB).1).1)
      ((Finset.mem_inter.mp ((hpair C).1 p hpC).1).1)
  refine ⟨Q, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    obtain ⟨B, _, hpB⟩ := Finset.mem_biUnion.mp hp
    have h := (hpair B).1 p hpB
    exact ⟨(Finset.mem_inter.mp h.1).2, (Finset.mem_inter.mp h.2.1).2, h.2.2⟩
  · intro p hp r hr hpr
    obtain ⟨B, hB, hpB⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨C, hC, hrC⟩ := Finset.mem_biUnion.mp hr
    by_cases hBC : B = C
    · subst C
      exact (hpair B).2 hpB hrC hpr
    · exact (hP hB hC hBC).mono (hsupport B p hpB) (hsupport C r hrC)
  · intro p hp
    obtain ⟨B, hB, hpB⟩ := Finset.mem_biUnion.mp hp
    exact (mem_sameBlockPairs P T p.1 p.2).mpr ⟨B, hB, (hpair B).1 p hpB⟩
  · change (P.biUnion pairs).card = blockPairCount P T
    rw [Finset.card_biUnion hdis]
    exact Finset.sum_congr rfl (fun B _ => hcard B)

theorem exists_block_pair_packing {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (T : Finset (Sym2 V)) :
    ∃ Q : Finset (Sym2 V × Sym2 V), IsPairPacking T Q ∧
      Q ⊆ sameBlockPairs P T ∧ Q.card = blockPairCount P T :=
  exists_block_pair_packing_of_disjoint P hP.2 T

/-- Repeated-edge volume supplies any prescribed number of disjoint pairs
up to one third of that volume. -/
theorem exists_repeated_edge_pairs_of_disjoint {V : Type*} [DecidableEq V]
    (P : Finset (RectangleBlock V))
    (hP : (P : Set (RectangleBlock V)).PairwiseDisjoint RectangleBlock.edges)
    (T : Finset (Sym2 V))
    (j : ℕ) (hj : 3 * j ≤ repeatedEdgeVolume P T) :
    ∃ Q : Finset (Sym2 V × Sym2 V), IsPairPacking T Q ∧
      Q ⊆ sameBlockPairs P T ∧ Q.card = j := by
  classical
  obtain ⟨Q, hQ, hQP, hcard⟩ := exists_block_pair_packing_of_disjoint P hP T
  have hbound := repeatedEdgeVolume_le_three_pairCount P T
  have hjQ : j ≤ Q.card := by omega
  obtain ⟨R, hRQ, hRcard⟩ := Finset.exists_subset_card_eq hjQ
  exact ⟨R, hQ.mono hRQ, hRQ.trans hQP, hRcard⟩

theorem exists_repeated_edge_pairs {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (T : Finset (Sym2 V))
    (j : ℕ) (hj : 3 * j ≤ repeatedEdgeVolume P T) :
    ∃ Q : Finset (Sym2 V × Sym2 V), IsPairPacking T Q ∧
      Q ⊆ sameBlockPairs P T ∧ Q.card = j :=
  exists_repeated_edge_pairs_of_disjoint P hP.2 T j hj

end Erdos911
