import Erdos911.CopyImages

namespace Erdos911

def inducedHostEdges {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (U : Finset W) : Finset (Sym2 W) :=
  H.edgeFinset.filter (fun e => e.toFinset ⊆ U)

theorem inducedHostEdges_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (U : Finset W) :
    (inducedHostEdges H U).card = (H.induce (U : Set W)).edgeSet.ncard := by
  rw [inducedHostEdges, H.card_filter_edgeFinset_toFinset_subset]
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]

theorem copyRawEdges_subset_inducedHostEdges {V W : Type*} [Fintype V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel H.Adj] (f : G.Copy H) :
    copyRawEdges f ⊆ inducedHostEdges H (copyVertices f) := by
  intro e he
  have hes : e ∈ f.toSubgraph.edgeSet := (mem_copyRawEdges_iff f e).mp he
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · exact (SimpleGraph.mem_edgeFinset).mpr (f.toSubgraph.edgeSet_subset hes)
  · intro w hw
    have hwe : w ∈ e := by simpa using hw
    have hwv := SimpleGraph.Subgraph.mem_verts_of_mem_edge hes hwe
    rw [← copyVertices_eq_subgraph_verts f] at hwv
    exact hwv

end Erdos911
