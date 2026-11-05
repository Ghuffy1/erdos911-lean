import Erdos911.HostDegreePruning
import Erdos911.DeletedEdgeCapacity

namespace Erdos911

noncomputable def eligibleCopyImages {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (K H J : SimpleGraph W) : Finset (Finset (Sym2 W)) := by
  classical
  exact ((Finset.univ : Finset (G.Copy K)).image copyRawEdges).filter
    (fun (E : Finset (Sym2 W)) => (E : Set (Sym2 W)) ⊆ (K \ H).edgeSet ∪ J.edgeSet)

theorem mem_eligibleCopyImages {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (K H J : SimpleGraph W) (E : Finset (Sym2 W)) :
    E ∈ eligibleCopyImages G K H J ↔
      (∃ f : G.Copy K, copyRawEdges f = E) ∧
        (E : Set (Sym2 W)) ⊆ (K \ H).edgeSet ∪ J.edgeSet := by
  classical
  simp only [eligibleCopyImages, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]

theorem eligibleCopyImages_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (K H J : SimpleGraph W) [DecidableRel K.Adj] :
    (eligibleCopyImages G K H J).card ≤ K.copyCount G := by
  classical
  have heq : eligibleCopyImages G K H J =
      ((Finset.univ : Finset (G.Copy K)).image copyRawEdges).filter
        (fun (E : Finset (Sym2 W)) => (E : Set (Sym2 W)) ⊆ (K \ H).edgeSet ∪ J.edgeSet) := by
    ext E
    simp only [mem_eligibleCopyImages, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  have hfilter : (eligibleCopyImages G K H J).card ≤
      ((Finset.univ : Finset (G.Copy K)).image copyRawEdges).card := by
    rw [heq]
    exact Finset.card_filter_le _ _
  exact hfilter.trans (copyRawEdges_image_card_le G K)

theorem eligible_image_residual_card {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (K H J : SimpleGraph W) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel J.Adj] (L : ℝ)
    (hdeleted : ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ L)
    (E : Finset (Sym2 W)) (hE : E ∈ eligibleCopyImages G K H J) :
    (G.edgeSet.ncard : ℝ) - L ≤ (retainedEdges J E).card := by
  classical
  obtain ⟨⟨f, rfl⟩, heligible⟩ := (mem_eligibleCopyImages G K H J E).mp hE
  have hsubset : copyRawEdges f ⊆ (K \ H).edgeFinset ∪ J.edgeFinset := by
    intro e he
    rcases heligible he with h | h
    · exact Finset.mem_union_left _ ((K \ H).mem_edgeFinset.mpr h)
    · exact Finset.mem_union_right _ (J.mem_edgeFinset.mpr h)
  have hcount := copy_capacity_union_inter (copyRawEdges f) (K \ H).edgeFinset J.edgeFinset
  rw [Finset.inter_eq_left.mpr hsubset, copyRawEdges_card] at hcount
  have hretained : (retainedEdges J (copyRawEdges f)).card = (copyRawEdges f ∩ J.edgeFinset).card := by
    rw [retainedEdges_card_eq_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_edgeFinset]
  have hreal : (G.edgeSet.ncard : ℝ) ≤
      (copyRawEdges f ∩ (K \ H).edgeFinset).card + (retainedEdges J (copyRawEdges f)).card := by
    rw [hretained]
    exact_mod_cast hcount
  linarith [hdeleted f]

theorem blue_copy_eligible {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (K H J : SimpleGraph W) (ω : J.edgeSet → Bool)
    (f : G.Copy (K \ (H \ edgeColorClass J ω true))) :
    copyRawEdges ((SimpleGraph.Copy.ofLE _ K sdiff_le).comp f) ∈ eligibleCopyImages G K H J := by
  classical
  apply (mem_eligibleCopyImages G K H J _).mpr
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro e he
  rw [copyRawEdges_ofLE_comp] at he
  have heblue := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e).mp he)
  rw [SimpleGraph.edgeSet_sdiff] at heblue
  by_cases heH : e ∈ H.edgeSet
  · have hetrue : e ∈ (edgeColorClass J ω true).edgeSet := by
      by_contra hfalse
      apply heblue.2
      rw [SimpleGraph.edgeSet_sdiff]
      exact ⟨heH, hfalse⟩
    have heJ : e ∈ J.edgeSet := SimpleGraph.edgeSet_mono (edgeColorClass_le J ω true) hetrue
    exact Or.inr heJ
  · apply Or.inl
    rw [SimpleGraph.edgeSet_sdiff]
    exact ⟨heblue.1, heH⟩

theorem blue_copy_residual_bits {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (K H J : SimpleGraph W) [DecidableRel J.Adj]
    (hJH : J ≤ H) (ω : J.edgeSet → Bool)
    (f : G.Copy (K \ (H \ edgeColorClass J ω true))) :
    ∀ e ∈ retainedEdges J (copyRawEdges ((SimpleGraph.Copy.ofLE _ K sdiff_le).comp f)), ω e = true := by
  classical
  intro e he
  have hecopy := (mem_retainedEdges J _ e).mp he
  rw [copyRawEdges_ofLE_comp] at hecopy
  have heblue := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e.val).mp hecopy)
  rw [SimpleGraph.edgeSet_sdiff] at heblue
  have heH : e.val ∈ H.edgeSet := SimpleGraph.edgeSet_mono hJH e.property
  apply (edgeColorClass_edge_iff J ω true e).mp
  by_contra hfalse
  apply heblue.2
  rw [SimpleGraph.edgeSet_sdiff]
  exact ⟨heH, hfalse⟩

end Erdos911
