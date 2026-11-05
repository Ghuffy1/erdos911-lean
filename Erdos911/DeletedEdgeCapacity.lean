import Erdos911.OrdinaryRoleEdges

namespace Erdos911

/-- The missing edges in the pulled-back target inject into the specified
deleted host edges used by that copy. -/
theorem copy_missing_edges_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) (K : Finset (Sym2 W))
    (hkeep : ∀ u v, H.Adj u v → s(u, v) ∉ K → J.Adj u v) :
    (F \ copyRetainedGraph J f).edgeFinset.card ≤ (copyRawEdges f ∩ K).card := by
  classical
  let R := copyRetainedGraph J f
  have hsub : ((F \ R).edgeFinset.image (Sym2.map (f : V → W))) ⊆ copyRawEdges f ∩ K := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    induction a using Sym2.inductionOn with
    | hf u v =>
      have hmissing : (F \ R).Adj u v := (SimpleGraph.mem_edgeFinset).mp ha
      have huv : F.Adj u v := hmissing.1
      have hK : s(f u, f v) ∈ K := by
        by_contra hn
        exact hmissing.2 ⟨huv, hkeep (f u) (f v) (map_rel f.toHom huv) hn⟩
      apply Finset.mem_inter.mpr
      refine ⟨?_, hK⟩
      exact (mem_copyRawEdges_iff_exists f _).mpr ⟨⟨s(u, v), huv⟩, rfl⟩
  have hinj : Function.Injective (Sym2.map (f : V → W)) :=
    Sym2.map.injective (show Function.Injective (f : V → W) from f.injective)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact hcard

theorem copy_capacity_union {W : Type*} [DecidableEq W]
    (T A B : Finset (Sym2 W)) : (T ∩ (A ∪ B)).card ≤ (T ∩ A).card + B.card := by
  have hsub : T ∩ (A ∪ B) ⊆ (T ∩ A) ∪ B := by
    intro e he
    obtain ⟨heT, heAB⟩ := Finset.mem_inter.mp he
    rcases Finset.mem_union.mp heAB with heA | heB
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨heT, heA⟩)
    · exact Finset.mem_union_right _ heB
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem copy_capacity_union_inter {W : Type*} [DecidableEq W]
    (T A B : Finset (Sym2 W)) :
    (T ∩ (A ∪ B)).card ≤ (T ∩ A).card + (T ∩ B).card := by
  have heq : T ∩ (A ∪ B) = (T ∩ A) ∪ (T ∩ B) := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_union, and_or_left]
  rw [heq]
  exact Finset.card_union_le _ _

/-- A deleted edge set with insufficient capacity for a blue target and
a red subgraph avoiding one of its subgraphs gives an avoiding coloring. -/
theorem avoiding_coloring_of_deleted_capacity {V U W : Type*}
    [Fintype V] [Fintype U] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (G : SimpleGraph U) (H : SimpleGraph W)
    (hFG : F.IsContained G) (K : Finset (Sym2 W))
    (hred : ¬F.IsContained (H.deleteEdges (K : Set (Sym2 W))))
    (hcapacity : ∀ f : G.Copy H, (copyRawEdges f ∩ K).card < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  let R := H.deleteEdges (K : Set (Sym2 W))
  refine ⟨R, H.deleteEdges_le _, fun hG => hred (hFG.trans hG), ?_⟩
  rintro ⟨f⟩
  let fH : G.Copy H := (SimpleGraph.Copy.ofLE _ H sdiff_le).comp f
  have hsub : copyRawEdges fH ⊆ K := by
    intro e he
    have hecopy : e ∈ copyRawEdges f := by simpa only [fH, copyRawEdges_ofLE_comp] using he
    have heblue := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e).mp hecopy)
    rw [SimpleGraph.edgeSet_sdiff] at heblue
    by_contra hn
    apply heblue.2
    change e ∈ (H.deleteEdges (K : Set (Sym2 W))).edgeSet
    rw [H.edgeSet_deleteEdges]
    exact ⟨heblue.1, hn⟩
  have heq : copyRawEdges fH ∩ K = copyRawEdges fH := Finset.inter_eq_left.mpr hsub
  have h := hcapacity fH
  rw [heq, copyRawEdges_card] at h
  exact Nat.lt_irrefl _ h

end Erdos911
