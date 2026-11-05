import Erdos911.CopySymmetry

namespace Erdos911

noncomputable def subgraphHostEdges {W : Type*} [Fintype W] (H : SimpleGraph W)
    (S : H.Subgraph) : Finset H.edgeSet := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ S.edgeSet)

noncomputable def copyHostEdges {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) : Finset H.edgeSet := by
  classical
  exact Finset.univ.map f.mapEdgeSet

theorem copyHostEdges_card {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) [DecidableRel G.Adj] {H : SimpleGraph W} (f : G.Copy H) :
    (copyHostEdges f).card = G.edgeFinset.card := by
  classical
  simp only [copyHostEdges, Finset.card_map, Finset.card_univ]
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]

theorem copyHostEdges_eq_subgraphHostEdges {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) :
    copyHostEdges f = subgraphHostEdges H f.toSubgraph := by
  classical
  ext e
  simp only [copyHostEdges, Finset.mem_map, Finset.mem_univ, true_and,
    subgraphHostEdges, Finset.mem_filter, true_and, SimpleGraph.Copy.toSubgraph,
    SimpleGraph.Subgraph.edgeSet_map, SimpleGraph.Subgraph.edgeSet_top, Set.mem_image]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.val, a.property, congrArg Subtype.val ha⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem copyHostEdges_image_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    ((Finset.univ : Finset (G.Copy H)).image copyHostEdges).card ≤ H.copyCount G := by
  classical
  calc
    ((Finset.univ : Finset (G.Copy H)).image copyHostEdges).card =
        (((Finset.univ : Finset (G.Copy H)).image SimpleGraph.Copy.toSubgraph).image
          (subgraphHostEdges H)).card := by
      congr 1
      rw [Finset.image_image]
      apply Finset.image_congr
      intro f _
      exact copyHostEdges_eq_subgraphHostEdges f
    _ ≤ _ := by
      rw [SimpleGraph.copyCount_eq_card_image_copyToSubgraph]
      exact Finset.card_image_le

def edgeColorClass {W : Type*} (H : SimpleGraph W) (ω : H.edgeSet → Bool) (b : Bool) :
    SimpleGraph W where
  Adj u v := ∃ h : H.Adj u v, ω ⟨s(u, v), h⟩ = b
  symm.symm u v h := by
    obtain ⟨h, hb⟩ := h
    refine ⟨h.symm, ?_⟩
    convert hb using 1
    congr 1
    exact Subtype.ext (Sym2.eq_swap)
  loopless.irrefl u h := H.loopless.irrefl u h.choose

theorem edgeColorClass_le {W : Type*} (H : SimpleGraph W) (ω : H.edgeSet → Bool) (b : Bool) :
    edgeColorClass H ω b ≤ H :=
  fun _ _ h => h.choose

theorem edgeColorClass_adj_iff {W : Type*} (H : SimpleGraph W)
    (ω : H.edgeSet → Bool) (b : Bool) {u v : W} (h : H.Adj u v) :
    (edgeColorClass H ω b).Adj u v ↔ ω ⟨s(u, v), h⟩ = b := by
  constructor
  · rintro ⟨_, hb⟩
    exact hb
  · intro hb
    exact ⟨h, hb⟩

theorem edgeColorClass_edge_iff {W : Type*} (H : SimpleGraph W)
    (ω : H.edgeSet → Bool) (b : Bool) (e : H.edgeSet) :
    e.val ∈ (edgeColorClass H ω b).edgeSet ↔ ω e = b := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf u v => exact edgeColorClass_adj_iff H ω b he

theorem edgeColorClass_complement {W : Type*} (H : SimpleGraph W) (ω : H.edgeSet → Bool) :
    H \ edgeColorClass H ω false = edgeColorClass H ω true := by
  ext u v
  by_cases h : H.Adj u v
  · simp only [SimpleGraph.sdiff_adj, edgeColorClass_adj_iff H ω false h,
      edgeColorClass_adj_iff H ω true h, h, true_and]
    cases ω ⟨s(u, v), h⟩ <;> decide
  · have hfalse : ¬(edgeColorClass H ω false).Adj u v := fun hb => h hb.choose
    have htrue : ¬(edgeColorClass H ω true).Adj u v := fun hb => h hb.choose
    simp only [SimpleGraph.sdiff_adj, h, hfalse, htrue, not_false_eq_true, and_true]

theorem colored_copyHostEdges {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} (H : SimpleGraph W) (ω : H.edgeSet → Bool) (b : Bool)
    (f : G.Copy (edgeColorClass H ω b)) :
    ∀ e ∈ copyHostEdges ((SimpleGraph.Copy.ofLE _ _ (edgeColorClass_le H ω b)).comp f),
      ω e = b := by
  classical
  intro e he
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp he
  apply (edgeColorClass_edge_iff H ω b _).mp
  exact (f.mapEdgeSet a).property

end Erdos911
