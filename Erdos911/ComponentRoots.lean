import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega

namespace Erdos911

noncomputable def componentRoot {V : Type*} (G : SimpleGraph V) (v : V) : V :=
  (G.connectedComponentMk v).out

theorem componentRoot_component {V : Type*} (G : SimpleGraph V) (v : V) :
    G.connectedComponentMk (componentRoot G v) = G.connectedComponentMk v :=
  (G.connectedComponentMk v).out_eq

theorem componentRoot_reachable {V : Type*} (G : SimpleGraph V) (v : V) :
    G.Reachable v (componentRoot G v) :=
  SimpleGraph.ConnectedComponent.exact (componentRoot_component G v).symm

theorem componentRoot_eq_of_adj {V : Type*} (G : SimpleGraph V) {u v : V}
    (h : G.Adj u v) : componentRoot G u = componentRoot G v := by
  exact congrArg (fun C : G.ConnectedComponent => C.out)
    (SimpleGraph.ConnectedComponent.sound h.reachable)

theorem componentRoot_idempotent {V : Type*} (G : SimpleGraph V) (v : V) :
    componentRoot G (componentRoot G v) = componentRoot G v := by
  exact congrArg (fun C : G.ConnectedComponent => C.out) (componentRoot_component G v)

theorem component_roots_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    (Finset.univ.filter (fun v => componentRoot G v = v)).card = Nat.card G.ConnectedComponent := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let e : G.ConnectedComponent ≃ {v : V // componentRoot G v = v} := {
    toFun := fun C => ⟨C.out, by
      have hC : G.connectedComponentMk C.out = C := C.out_eq
      exact congrArg (fun C : G.ConnectedComponent => C.out) hC⟩
    invFun := fun v => G.connectedComponentMk v.val
    left_inv := fun C => C.out_eq
    right_inv := by
      intro v
      apply Subtype.ext
      exact v.property }
  calc
    (Finset.univ.filter (fun v => componentRoot G v = v)).card =
        Fintype.card {v : V // componentRoot G v = v} := by
      symm
      exact Fintype.card_ofFinset _ (fun v => by
        change v ∈ Finset.univ.filter (fun v => componentRoot G v = v) ↔ componentRoot G v = v
        simp)
    _ = Fintype.card G.ConnectedComponent := Fintype.card_congr e.symm
    _ = Nat.card G.ConnectedComponent := Nat.card_eq_fintype_card.symm

theorem components_lt_vertices_of_adj {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hedge : ∃ u v, G.Adj u v) :
    Nat.card G.ConnectedComponent < Fintype.card V := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hleft : Function.LeftInverse G.connectedComponentMk
      (fun C : G.ConnectedComponent => C.out) := fun C => C.out_eq
  rw [Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective _ hleft.injective
  intro hsurj
  have hfixed : ∀ v, componentRoot G v = v := by
    intro v
    obtain ⟨C, rfl⟩ := hsurj v
    have hC : G.connectedComponentMk C.out = C := C.out_eq
    exact congrArg (fun C : G.ConnectedComponent => C.out) hC
  obtain ⟨u, v, huv⟩ := hedge
  have h := componentRoot_eq_of_adj G huv
  rw [hfixed u, hfixed v] at h
  exact huv.ne h

/-- Every nonroot vertex has a neighbor closer to the chosen root of its
connected component. -/
theorem exists_neighbor_closer_to_root {V : Type*} (G : SimpleGraph V) (v : V)
    (hv : v ≠ componentRoot G v) :
    ∃ u, G.Adj v u ∧ G.dist (componentRoot G u) u < G.dist (componentRoot G v) v := by
  obtain ⟨p, hp⟩ := (componentRoot_reachable G v).exists_walk_length_eq_dist
  have hnil : ¬p.Nil := fun h => hv h.eq
  let u := p.snd
  have hadj : G.Adj v u := p.adj_snd hnil
  have hroot : componentRoot G u = componentRoot G v :=
    (componentRoot_eq_of_adj G hadj).symm
  have htail := p.length_tail_add_one hnil
  have hdist := G.dist_le p.tail
  refine ⟨u, hadj, ?_⟩
  rw [hroot, G.dist_comm (u := componentRoot G v) (v := u),
    G.dist_comm (u := componentRoot G v) (v := v)]
  change G.dist p.snd (componentRoot G v) < G.dist v (componentRoot G v)
  omega

noncomputable def forestOrderKey {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ ×ₗ ℕ :=
  toLex (G.dist (componentRoot G v) v, (Fintype.equivFin V v).val)

theorem forestOrderKey_injective {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Function.Injective (forestOrderKey G) := by
  intro u v huv
  apply (Fintype.equivFin V).injective
  apply Fin.ext
  exact congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) huv

theorem exists_smaller_neighbor_key {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) (hv : v ≠ componentRoot G v) :
    ∃ u, G.Adj u v ∧ forestOrderKey G u < forestOrderKey G v := by
  obtain ⟨u, hadj, hdist⟩ := exists_neighbor_closer_to_root G v hv
  refine ⟨u, hadj.symm, ?_⟩
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hdist)

/-- Enumerate a finite type in the order of an injective ranking key. -/
theorem exists_equiv_ordered_by_key {V K : Type*} [Fintype V] [LinearOrder K]
    (key : V → K) (hkey : Function.Injective key) :
    ∃ e : Fin (Fintype.card V) ≃ V,
      ∀ i j, key (e i) < key (e j) ↔ i < j := by
  let : LinearOrder V := LinearOrder.lift' key hkey
  let e := Fintype.orderIsoFinOfCardEq V rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i j
  change e i < e j ↔ i < j
  exact e.lt_iff_lt

end Erdos911
