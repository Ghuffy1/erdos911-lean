import Erdos911.ComponentModels
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Erdos911

noncomputable def componentSide {V : Type*} [Fintype V] (G : SimpleGraph V)
    (t : ComponentType G) (S : Finset V) : Finset (componentRepresentative G t).supp := by
  classical
  exact Finset.univ.filter (fun v => v.val ∈ S)

theorem mem_componentSide {V : Type*} [Fintype V] (G : SimpleGraph V)
    (t : ComponentType G) (S : Finset V) (v : (componentRepresentative G t).supp) :
    v ∈ componentSide G t S ↔ v.val ∈ S := by
  classical
  simp only [componentSide, Finset.mem_filter, Finset.mem_univ, true_and]

theorem componentModel_degree_eq {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (t : ComponentType G) [DecidableRel (componentModel G t).Adj]
    (v : (componentRepresentative G t).supp) : (componentModel G t).degree v = G.degree v.val := by
  have h := component_neighbor_ncard_eq G (componentRepresentative G t) v
  have h' : ((componentModel G t).neighborSet v).ncard = (G.neighborSet v.val).ncard := h
  simpa only [SimpleGraph.ncard_neighborSet] using h'

theorem componentSide_bipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (t : ComponentType G) :
    (componentModel G t).IsBipartiteWith
      (componentSide G t left : Set (componentRepresentative G t).supp)
      (componentSide G t right : Set (componentRepresentative G t).supp) := by
  classical
  constructor
  · apply Set.disjoint_left.mpr
    intro v hvL hvR
    exact Set.disjoint_left.mp hB.disjoint ((mem_componentSide G t left v).mp hvL)
      ((mem_componentSide G t right v).mp hvR)
  · intro u v huv
    rcases hB.mem_of_adj (show G.Adj u.val v.val from huv) with h | h
    · exact Or.inl ⟨(mem_componentSide G t left u).mpr h.1, (mem_componentSide G t right v).mpr h.2⟩
    · exact Or.inr ⟨(mem_componentSide G t right u).mpr h.1, (mem_componentSide G t left v).mpr h.2⟩

theorem bipartite_right_isVertexCover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) : G.IsVertexCover (right : Set V) := by
  intro u v huv
  rcases hB.mem_of_adj huv with h | h
  · exact Or.inr h.2
  · exact Or.inl h.1

theorem bipartite_partition_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V))
    (hneighbors : ∀ v, ∃ w, G.Adj v w) : left.card + right.card = Fintype.card V := by
  classical
  have hd : Disjoint left right := Finset.disjoint_left.mpr (Set.disjoint_left.mp hB.disjoint)
  have hu : left ∪ right = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨w, hvw⟩ := hneighbors v
    rcases hB.mem_of_adj hvw with h | h
    · exact Finset.mem_union_left _ h.1
    · exact Finset.mem_union_right _ h.1
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]

theorem bipartite_exact_right_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (d : ℕ)
    (hdegree : ∀ v ∈ right, G.degree v = d) : G.edgeSet.ncard = d * right.card := by
  classical
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hB
  have hconstant : (∑ v ∈ right, G.degree v) = right.card * d := by
    calc
      _ = ∑ _v ∈ right, d := Finset.sum_congr rfl hdegree
      _ = _ := by simp
  rw [hconstant, G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
  exact hsum.symm.trans (Nat.mul_comm _ _)

theorem componentSide_right_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (d : ℕ)
    (hdegree : ∀ v ∈ right, G.degree v = d) (t : ComponentType G) :
    componentSize G t = d * (componentSide G t right).card := by
  classical
  apply bipartite_exact_right_edge_count (componentModel G t) (componentSide G t left)
    (componentSide G t right) (componentSide_bipartite G left right hB t) d
  intro v hv
  rw [componentModel_degree_eq]
  exact hdegree v.val ((mem_componentSide G t right v).mp hv)

theorem componentSide_partition_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V))
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (t : ComponentType G) :
    (componentSide G t left).card + (componentSide G t right).card = componentOrder G t := by
  classical
  rw [componentOrder, Nat.card_eq_fintype_card]
  apply bipartite_partition_card (componentModel G t) (componentSide G t left)
    (componentSide G t right) (componentSide_bipartite G left right hB t)
  intro v
  obtain ⟨w, hvw⟩ := hneighbors v.val
  exact ⟨⟨w, (componentRepresentative G t).mem_supp_of_adj_mem_supp v.property hvw⟩, hvw⟩

theorem componentSide_card_eq_of_class {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V))
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ v ∈ right, G.degree v = d) (s t : ComponentType G)
    (horder : componentOrder G s = componentOrder G t) (hedge : componentSize G s = componentSize G t) :
    (componentSide G s right).card = (componentSide G t right).card ∧
      (componentSide G s left).card = (componentSide G t left).card := by
  have hs := componentSide_right_edge_count G left right hB d hdegree s
  have ht := componentSide_right_edge_count G left right hB d hdegree t
  have hr : (componentSide G s right).card = (componentSide G t right).card :=
    (Nat.mul_left_cancel_iff hd).mp (by omega)
  have hsp := componentSide_partition_card G left right hB hneighbors s
  have htp := componentSide_partition_card G left right hB hneighbors t
  exact ⟨hr, by omega⟩

end Erdos911
