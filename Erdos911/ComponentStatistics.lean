import Erdos911.ComponentModels

namespace Erdos911

theorem component_vertex_count_sum {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] :
    (∑ c : G.ConnectedComponent, Nat.card c.supp) = Fintype.card V := by
  classical
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
  rw [Nat.card_sigma] at h
  calc
    (∑ c : G.ConnectedComponent, Nat.card c.supp) =
        ∑ c : G.ConnectedComponent, Nat.card {v // G.connectedComponentMk v = c} := by
      apply Finset.sum_congr rfl
      intro c _
      rfl
    _ = Nat.card V := h
    _ = Fintype.card V := Nat.card_eq_fintype_card

theorem component_edge_count_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent] :
    (∑ c : G.ConnectedComponent, (G.induce c.supp).edgeSet.ncard) = G.edgeSet.ncard := by
  classical
  have hdegrees (c : G.ConnectedComponent) :
      (∑ v : c.supp, G.degree v.val) = 2 * (G.induce c.supp).edgeSet.ncard := by
    calc
      (∑ v : c.supp, G.degree v.val) = ∑ v : c.supp, (G.induce c.supp).degree v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [← (G.induce c.supp).ncard_neighborSet v, component_neighbor_ncard_eq,
          G.ncard_neighborSet]
      _ = 2 * (G.induce c.supp).edgeFinset.card :=
        (G.induce c.supp).sum_degrees_eq_twice_card_edges
      _ = 2 * (G.induce c.supp).edgeSet.ncard := by
        rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have hsum := Fintype.sum_fiberwise G.connectedComponentMk (fun v => G.degree v)
  change (∑ c : G.ConnectedComponent, ∑ v : c.supp, G.degree v.val) = ∑ v, G.degree v at hsum
  simp_rw [hdegrees] at hsum
  rw [← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges,
    G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
  omega

theorem component_type_weighted_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.ConnectedComponent] (w : ComponentType G → ℕ) :
    (∑ t : ComponentType G, componentMultiplicity G t * w t) =
      ∑ c : G.ConnectedComponent, w (componentTypeOf G c) := by
  classical
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    ← Nat.card_eq_fintype_card, componentMultiplicity] using
    Fintype.sum_fiberwise' (componentTypeOf G) w

theorem component_order_mass {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∑ t : ComponentType G, componentMultiplicity G t * componentOrder G t) =
      Fintype.card V := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [component_type_weighted_sum]
  simpa only [← component_order_eq_model] using component_vertex_count_sum G

theorem component_size_mass {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ t : ComponentType G, componentMultiplicity G t * componentSize G t) =
      G.edgeSet.ncard := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [component_type_weighted_sum]
  simpa only [← component_size_eq_model] using component_edge_count_sum G

theorem componentOrder_pos {V : Type*} [Fintype V] (G : SimpleGraph V) (t : ComponentType G) :
    0 < componentOrder G t := by
  rw [componentOrder, Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr (componentModel_connected G t).nonempty

theorem component_degree_sum_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hmin : ∀ v, d ≤ G.degree v) (t : ComponentType G) :
    d * componentOrder G t ≤ 2 * componentSize G t := by
  classical
  let F := componentModel G t
  have hFmin : ∀ v, d ≤ F.degree v := by
    intro v
    have h := (componentModel_degree_bounds G d G.maxDegree hmin G.degree_le_maxDegree t v).1
    simpa only [SimpleGraph.ncard_neighborSet] using h
  have hsum : d * Fintype.card (componentRepresentative G t).supp ≤ 2 * F.edgeFinset.card := by
    calc
      d * Fintype.card (componentRepresentative G t).supp = ∑ _ : (componentRepresentative G t).supp, d := by
        simp [mul_comm]
      _ ≤ ∑ v, F.degree v := Finset.sum_le_sum (fun v _ => hFmin v)
      _ = 2 * F.edgeFinset.card := F.sum_degrees_eq_twice_card_edges
  simpa only [componentOrder, componentSize, Nat.card_eq_fintype_card,
    SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard, F] using hsum

theorem componentSize_pos {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, 1 ≤ G.degree v) (t : ComponentType G) : 0 < componentSize G t := by
  have h := component_degree_sum_bound G 1 hmin t
  have hk := componentOrder_pos G t
  omega

end Erdos911
