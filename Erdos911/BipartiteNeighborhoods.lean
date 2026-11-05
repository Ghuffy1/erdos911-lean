import Erdos911.NeighborhoodTransport
import Erdos911.IncidenceGraph
import Erdos911.BipartiteRestriction

namespace Erdos911

noncomputable def bipartiteNeighborhoods {V : Type*} [Fintype V]
    (G : SimpleGraph V) (left right : Finset V) (y : ↥right) : Finset ↥left := by
  classical
  exact Finset.univ.filter (fun x => G.Adj x.val y.val)

theorem mem_bipartiteNeighborhoods {V : Type*} [Fintype V]
    (G : SimpleGraph V) (left right : Finset V) (y : ↥right) (x : ↥left) :
    x ∈ bipartiteNeighborhoods G left right y ↔ G.Adj x.val y.val := by
  classical
  simp only [bipartiteNeighborhoods, Finset.mem_filter, Finset.mem_univ, true_and]

theorem bipartiteNeighborhoods_row_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (y : ↥right) :
    (bipartiteNeighborhoods G left right y).card = G.degree y.val := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact (G.mem_neighborFinset y.val x.val).mpr ((mem_bipartiteNeighborhoods G left right y x).mp hx).symm
  · intro x _ z _ hxz
    exact Subtype.ext hxz
  · intro v hv
    have hy := (G.mem_neighborFinset y.val v).mp hv
    refine ⟨⟨v, hB.symm.mem_of_mem_adj y.property hy⟩, ?_, rfl⟩
    exact (mem_bipartiteNeighborhoods G left right y _).mpr hy.symm

theorem bipartiteNeighborhoods_column_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (x : ↥left) :
    ((Finset.univ : Finset ↥right).filter
      (fun y => x ∈ bipartiteNeighborhoods G left right y)).card = G.degree x.val := by
  classical
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    exact (G.mem_neighborFinset x.val y.val).mpr
      ((mem_bipartiteNeighborhoods G left right y x).mp (Finset.mem_filter.mp hy).2)
  · intro y _ z _ hyz
    exact Subtype.ext hyz
  · intro v hv
    have hx := (G.mem_neighborFinset x.val v).mp hv
    refine ⟨⟨v, hB.mem_of_mem_adj x.property hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (mem_bipartiteNeighborhoods G left right _ x).mpr hx

noncomputable def bipartiteNeighborhoods_copy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) :
    (incidenceGraph (bipartiteNeighborhoods G left right)).Copy G where
  toHom := {
    toFun := Sum.elim Subtype.val Subtype.val
    map_rel' := by
      intro u v huv
      cases u with
      | inl x =>
        cases v with
        | inl z => exact huv.elim
        | inr y => exact (mem_bipartiteNeighborhoods G left right y x).mp huv
      | inr y =>
        cases v with
        | inl x => exact ((mem_bipartiteNeighborhoods G left right y x).mp huv).symm
        | inr z => exact huv.elim
  }
  injective' := by
    intro u v h
    cases u with
    | inl x =>
      cases v with
      | inl z => exact congrArg Sum.inl (Subtype.ext h)
      | inr y =>
        change x.val = y.val at h
        have hx : x.val ∈ right := by rw [h]; exact y.property
        exact (Set.disjoint_left.mp hB.disjoint x.property hx).elim
    | inr y =>
      cases v with
      | inl x =>
        change y.val = x.val at h
        have hx : x.val ∈ right := by rw [← h]; exact y.property
        exact (Set.disjoint_left.mp hB.disjoint x.property hx).elim
      | inr z => exact congrArg Sum.inr (Subtype.ext h)

theorem bipartiteNeighborhoods_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) :
    (incidenceGraph (bipartiteNeighborhoods G left right)).edgeFinset.card = G.edgeSet.ncard := by
  rw [incidenceGraph_edge_count]
  simp_rw [bipartiteNeighborhoods_row_card G left right hB]
  rw [Finset.sum_coe_sort right (fun v => G.degree v)]
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hB
  rwa [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at h

/-- Normalize the right degrees of a bipartite graph while retaining a
controlled left degree and a definite fraction of its edge count. -/
theorem exists_normalized_bipartite_copy {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (q a b r : ℕ)
    (hq : ∀ y ∈ right, q ≤ G.degree y) (ha : ∀ x ∈ left, G.degree x ≤ a)
    (hb : ∀ y ∈ right, G.degree y ≤ b) (hr : ∀ x ∈ left, r ≤ G.degree x)
    (hc : Real.exp 1 * Real.exp (-((q : ℝ) / b * r) / 8) * ((a * b : ℕ) + 1) ≤ 1) :
    ∃ S : ↥right → Finset ↥left,
      (incidenceGraph S).IsContained G ∧
      (∀ y, (incidenceGraph S).degree (Sum.inr y) = q) ∧
      (∀ x, (q : ℝ) / b * r / 2 < (incidenceGraph S).degree (Sum.inl x)) ∧
      (incidenceGraph S).edgeFinset.card = q * right.card ∧
      (q : ℝ) * G.edgeSet.ncard ≤ b * (incidenceGraph S).edgeFinset.card := by
  classical
  let N := bipartiteNeighborhoods G left right
  obtain ⟨S, hS, hleft⟩ := exists_degree_normalization_general N q a b r
    (fun y => by rw [bipartiteNeighborhoods_row_card G left right hB]; exact hq y.val y.property)
    (fun x => by rw [bipartiteNeighborhoods_column_card G left right hB]; exact ha x.val x.property)
    (fun y => by rw [bipartiteNeighborhoods_row_card G left right hB]; exact hb y.val y.property)
    (fun x => by rw [bipartiteNeighborhoods_column_card G left right hB]; exact hr x.val x.property) hc
  have hedge : (incidenceGraph S).edgeFinset.card = q * right.card := by
    rw [incidenceGraph_edge_count]
    simp only [(hS _).2, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
    exact Nat.mul_comm _ _
  have hbound : G.edgeSet.ncard ≤ b * right.card := by
    rw [← bipartiteNeighborhoods_edge_count G left right hB, incidenceGraph_edge_count]
    calc
      _ ≤ ∑ _y : ↥right, b := Finset.sum_le_sum (fun y _ => by
        rw [bipartiteNeighborhoods_row_card G left right hB]; exact hb y.val y.property)
      _ = _ := by simp [Nat.mul_comm]
  refine ⟨S, ?_, ?_, ?_, hedge, ?_⟩
  · exact ⟨(bipartiteNeighborhoods_copy G left right hB).comp
      (SimpleGraph.Copy.ofLE _ _ (incidenceGraph_mono (fun y => (hS y).1)))⟩
  · intro y
    rw [incidenceGraph_degree_right]
    exact (hS y).2
  · intro x
    simpa only [incidenceGraph_degree_left] using hleft x
  · rw [hedge]
    have hboundR : (G.edgeSet.ncard : ℝ) ≤ (b : ℝ) * right.card := by exact_mod_cast hbound
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left hboundR (Nat.cast_nonneg (α := ℝ) q)]

end Erdos911
