import Erdos911.CopyDensity
import Erdos911.BipartiteRestriction

namespace Erdos911

theorem degree_induce_support {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : G.support) :
    (G.induce G.support).degree v = G.degree v :=
  G.degree_induce_of_neighborSet_subset (G.neighborSet_subset_support v.val)

theorem edge_ncard_induce_support {V : Type*} [Fintype V]
    (G : SimpleGraph V) : (G.induce G.support).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  rw [← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card,
    ← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card]
  exact G.card_edgeFinset_induce_support

theorem support_card_pos_of_edge_ncard_pos {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (he : 0 < G.edgeSet.ncard) : 0 < Fintype.card G.support := by
  classical
  obtain ⟨e, he⟩ := (Set.ncard_pos (s := G.edgeSet)).mp he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have h : G.Adj u v := G.mem_edgeSet.mp he
    exact Fintype.card_pos_iff.mpr ⟨⟨u, v, h⟩⟩

theorem activeSide_bipartite {V : Type*}
    (G : SimpleGraph V) (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) :
    G.IsBipartiteWith (activeSide G left : Set V) (activeSide G right : Set V) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro v hL hR
    exact Set.disjoint_left.mp hB.disjoint
      ((mem_activeSide G left v).mp hL).1 ((mem_activeSide G right v).mp hR).1
  · intro u v huv
    have hu : u ∈ G.support := ⟨v, huv⟩
    have hv : v ∈ G.support := ⟨u, huv.symm⟩
    rcases hB.mem_of_adj huv with h | h
    · exact Or.inl ⟨(mem_activeSide G left u).mpr ⟨h.1, hu⟩,
        (mem_activeSide G right v).mpr ⟨h.2, hv⟩⟩
    · exact Or.inr ⟨(mem_activeSide G right u).mpr ⟨h.1, hu⟩,
        (mem_activeSide G left v).mpr ⟨h.2, hv⟩⟩

end Erdos911
