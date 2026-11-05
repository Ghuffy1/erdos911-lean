import Erdos911.ComponentMultiplicity
import Erdos911.CopyImages

namespace Erdos911

noncomputable def componentRepresentative {V : Type*} (G : SimpleGraph V)
    (t : ComponentType G) : G.ConnectedComponent := Quotient.out t

noncomputable instance componentModelVerticesFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ComponentType G) : Fintype (componentRepresentative G t).supp :=
  Fintype.ofFinite _

theorem componentRepresentative_type {V : Type*} (G : SimpleGraph V) (t : ComponentType G) :
    componentTypeOf G (componentRepresentative G t) = t := Quotient.out_eq t

noncomputable def componentModel {V : Type*} (G : SimpleGraph V) (t : ComponentType G) :
    SimpleGraph (componentRepresentative G t).supp :=
  G.induce (componentRepresentative G t).supp

noncomputable def componentOrder {V : Type*} (G : SimpleGraph V) (t : ComponentType G) : ℕ :=
  Nat.card (componentRepresentative G t).supp

noncomputable def componentSize {V : Type*} (G : SimpleGraph V) (t : ComponentType G) : ℕ :=
  (componentModel G t).edgeSet.ncard

theorem componentModel_connected {V : Type*} (G : SimpleGraph V) (t : ComponentType G) :
    (componentModel G t).Connected :=
  (componentRepresentative G t).connected_toSimpleGraph

theorem componentModel_iso_iff {V : Type*} (G : SimpleGraph V) (s t : ComponentType G) :
    Nonempty (componentModel G s ≃g componentModel G t) ↔ s = t := by
  change Nonempty (G.induce (componentRepresentative G s).supp ≃g
    G.induce (componentRepresentative G t).supp) ↔ s = t
  rw [← componentTypeOf_eq_iff, componentRepresentative_type, componentRepresentative_type]

theorem component_iso_model {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent) :
    Nonempty (G.induce c.supp ≃g componentModel G (componentTypeOf G c)) := by
  apply (componentTypeOf_eq_iff G c _).mp
  exact (componentRepresentative_type G (componentTypeOf G c)).symm

theorem component_order_eq_model {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent) :
    Nat.card c.supp = componentOrder G (componentTypeOf G c) := by
  obtain ⟨e⟩ := component_iso_model G c
  exact Nat.card_congr e.toEquiv

theorem component_size_eq_model {V : Type*} [Fintype V]
    (G : SimpleGraph V) (c : G.ConnectedComponent) :
    (G.induce c.supp).edgeSet.ncard = componentSize G (componentTypeOf G c) := by
  classical
  obtain ⟨e⟩ := component_iso_model G c
  have h := Nat.card_congr e.mapEdgeSet
  simpa only [componentSize, Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard] using h

theorem component_neighbor_ncard_eq {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c : G.ConnectedComponent) (v : c.supp) :
    ((G.induce c.supp).neighborSet v).ncard = (G.neighborSet v.val).ncard := by
  classical
  have h := G.degree_induce_of_neighborSet_subset
    (fun _ hw => c.mem_supp_of_adj_mem_supp v.property hw)
  simpa only [SimpleGraph.ncard_neighborSet] using h

theorem componentModel_degree_bounds {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d D : ℕ) (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ D)
    (t : ComponentType G) :
    ∀ v, d ≤ ((componentModel G t).neighborSet v).ncard ∧
      ((componentModel G t).neighborSet v).ncard ≤ D := by
  classical
  intro v
  change d ≤ ((G.induce (componentRepresentative G t).supp).neighborSet v).ncard ∧
    ((G.induce (componentRepresentative G t).supp).neighborSet v).ncard ≤ D
  rw [component_neighbor_ncard_eq, G.ncard_neighborSet]
  exact ⟨hmin v.val, hmax v.val⟩

end Erdos911
