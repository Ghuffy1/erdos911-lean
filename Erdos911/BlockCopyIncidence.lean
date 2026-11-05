import Erdos911.MixedBlockPacking
import Erdos911.AnchoredCopyCounting

namespace Erdos911

noncomputable def touchedBlocks {W : Type*} (P : Finset (RectangleBlock W))
    (T : Finset (Sym2 W)) : Finset P := by
  classical
  exact Finset.univ.filter (fun B => ¬Disjoint B.val.edges T)

theorem mem_touchedBlocks {W : Type*} (P : Finset (RectangleBlock W))
    (T : Finset (Sym2 W)) (B : P) :
    B ∈ touchedBlocks P T ↔ ¬Disjoint B.val.edges T := by
  classical
  simp only [touchedBlocks, Finset.mem_filter, Finset.mem_univ, true_and]

theorem touchedBlocks_card {W : Type*} [DecidableEq W] (P : Finset (RectangleBlock W))
    (T : Finset (Sym2 W)) :
    (touchedBlocks P T).card = ∑ B : P, if ¬Disjoint B.val.edges T then 1 else 0 := by
  classical
  unfold touchedBlocks
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases h : Disjoint B.val.edges T <;>
    simp only [h, not_true_eq_false, not_false_eq_true, ite_true, ite_false]

theorem block_used_edges_sum_eq {W : Type*} [DecidableEq W]
    (P : Finset (RectangleBlock W))
    (hP : (P : Set (RectangleBlock W)).PairwiseDisjoint RectangleBlock.edges)
    (T : Finset (Sym2 W)) :
    (T ∩ blockEdgeUnion P).card = ∑ B : P, (B.val.edges ∩ T).card := by
  classical
  have hdis : (P : Set (RectangleBlock W)).PairwiseDisjoint (fun B => B.edges ∩ T) := by
    intro B hB C hC hBC
    exact (hP hB hC hBC).mono Finset.inter_subset_left Finset.inter_subset_left
  have heq : P.biUnion (fun B => B.edges ∩ T) = T ∩ blockEdgeUnion P := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_inter, mem_blockEdgeUnion]
    aesop
  rw [← heq, Finset.card_biUnion hdis]
  exact (Finset.sum_coe_sort P _).symm

/-- The edges in blocks with repeated use account for every loss from
the number of used edges to the number of distinct touched blocks. -/
theorem block_edges_le_touched_add_repeated {W : Type*} [DecidableEq W]
    (P : Finset (RectangleBlock W))
    (hP : (P : Set (RectangleBlock W)).PairwiseDisjoint RectangleBlock.edges)
    (T : Finset (Sym2 W)) :
    (T ∩ blockEdgeUnion P).card ≤ (touchedBlocks P T).card + repeatedEdgeVolume P T := by
  classical
  rw [block_used_edges_sum_eq P hP T]
  have hterm (B : P) : (B.val.edges ∩ T).card ≤
      (if ¬Disjoint B.val.edges T then 1 else 0) +
        (if 2 ≤ (B.val.edges ∩ T).card then (B.val.edges ∩ T).card else 0) := by
    by_cases hdis : Disjoint B.val.edges T
    · rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
      exact Nat.zero_le _
    · have hpos : 0 < (B.val.edges ∩ T).card := by
        apply Finset.card_pos.mpr
        exact Finset.not_disjoint_iff_nonempty_inter.mp hdis
      simp only [hdis, not_false_eq_true, ite_true]
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset P)) => hterm B)
  rw [Finset.sum_add_distrib] at hsum
  have hrepeat : (∑ B : P, if 2 ≤ (B.val.edges ∩ T).card then (B.val.edges ∩ T).card else 0) =
      repeatedEdgeVolume P T := by
    exact Finset.sum_coe_sort P
      (fun B => if 2 ≤ (B.edges ∩ T).card then (B.edges ∩ T).card else 0)
  rw [hrepeat, ← touchedBlocks_card P T] at hsum
  exact hsum

theorem touchedBlocks_card_le {W : Type*} [DecidableEq W]
    (P : Finset (RectangleBlock W))
    (hP : (P : Set (RectangleBlock W)).PairwiseDisjoint RectangleBlock.edges)
    (T : Finset (Sym2 W)) : (touchedBlocks P T).card ≤ T.card := by
  classical
  have hterm (B : P) : (if ¬Disjoint B.val.edges T then 1 else 0) ≤
      (B.val.edges ∩ T).card := by
    by_cases h : Disjoint B.val.edges T
    · simp only [h, not_true_eq_false, ite_false, Nat.zero_le]
    · simp only [h, not_false_eq_true, ite_true]
      exact Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp h)
  have hsum := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset P)) => hterm B)
  have hle : (touchedBlocks P T).card ≤ ∑ B ∈ P, (B.edges ∩ T).card := by
    rw [← touchedBlocks_card P T] at hsum
    exact hsum.trans_eq (Finset.sum_coe_sort P (fun B => (B.edges ∩ T).card))
  exact hle.trans (block_used_edges_sum_le_of_disjoint P hP T)

theorem copy_touches_block_iff {V W : Type*} [Fintype V] [Fintype W]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (B : RectangleBlock W) :
    ¬Disjoint B.edges (copyRawEdges f) ↔
      ∃ e ∈ blockHostEdges H B, e ∈ copyHostEdges f := by
  classical
  constructor
  · intro h
    obtain ⟨e, heB, hef⟩ := Finset.not_disjoint_iff.mp h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hef
    exact ⟨a, (mem_blockHostEdges H B a).mpr heB, ha⟩
  · rintro ⟨e, heB, hef⟩
    apply Finset.not_disjoint_iff.mpr
    exact ⟨e.val, (mem_blockHostEdges H B e).mp heB,
      Finset.mem_map.mpr ⟨e, hef, rfl⟩⟩

theorem blockHostEdges_card_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) (B : RectangleBlock W) :
    (blockHostEdges H B).card ≤ B.edges.card := by
  classical
  have hsub : (blockHostEdges H B).map ⟨Subtype.val, Subtype.val_injective⟩ ⊆ B.edges := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    exact (mem_blockHostEdges H B a).mp ha
  simpa only [Finset.card_map] using Finset.card_le_card hsub

/-- Anchoring an edge in a block bounds the number of connected target
copies that can use this block. -/
theorem copy_block_incidence_bound {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (D M : ℕ) (hD : ∀ w, H.degree w ≤ D) (B : RectangleBlock W)
    (hB : B.edges.card ≤ M) :
    ((Finset.univ : Finset (F.Copy H)).filter
      (fun f => ¬Disjoint B.edges (copyRawEdges f))).card ≤
        M * (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) := by
  classical
  let uses (e : H.edgeSet) := (Finset.univ : Finset (F.Copy H)).filter
    (fun f => e ∈ copyHostEdges f)
  have hsub : ((Finset.univ : Finset (F.Copy H)).filter
      (fun f => ¬Disjoint B.edges (copyRawEdges f))) ⊆
      (blockHostEdges H B).biUnion uses := by
    intro f hf
    obtain ⟨e, heB, hef⟩ := (copy_touches_block_iff f B).mp (Finset.mem_filter.mp hf).2
    exact Finset.mem_biUnion.mpr ⟨e, heB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hef⟩⟩
  calc
    _ ≤ ((blockHostEdges H B).biUnion uses).card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ blockHostEdges H B, (uses e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ blockHostEdges H B,
        Fintype.card V * D ^ (2 * (Fintype.card V - 1)) :=
      Finset.sum_le_sum (fun e _ => copy_edge_incidence_bound F H hF D hD e)
    _ = (blockHostEdges H B).card *
        (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) := by simp
    _ ≤ M * (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) :=
      Nat.mul_le_mul_right _ ((blockHostEdges_card_le H B).trans hB)

end Erdos911
