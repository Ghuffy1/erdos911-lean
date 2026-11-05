import Erdos911.ConnectedLabelWeights

namespace Erdos911

noncomputable def connectedSetsOfOrder {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (u : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun S => S.card = u ∧ (F.induce (S : Set V)).Connected)

theorem connectedSetsOfOrder_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (D u : ℕ) (hD : ∀ v, F.degree v ≤ D) :
    (connectedSetsOfOrder F u).card ≤ Fintype.card V * D ^ (2 * (u - 1)) := by
  classical
  have hsub : connectedSetsOfOrder F u ⊆
      (Finset.univ : Finset V).biUnion (fun v => rootedConnectedSets F v u) := by
    intro S hS
    obtain ⟨hcard, hconn⟩ := (Finset.mem_filter.mp hS).2
    obtain ⟨v⟩ := hconn.nonempty
    exact Finset.mem_biUnion.mpr ⟨v.val, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.property, hcard, hconn⟩⟩
  calc
    _ ≤ ((Finset.univ : Finset V).biUnion (fun v => rootedConnectedSets F v u)).card := Finset.card_le_card hsub
    _ ≤ ∑ v, (rootedConnectedSets F v u).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : V, D ^ (2 * (u - 1)) :=
      Finset.sum_le_sum (fun v _ => rooted_connected_set_count F D hD v u)
    _ = _ := by simp

noncomputable def paletteBadSets {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (d : ℕ) : Finset (Finset V) := by
  classical
  exact (smallConnectedSets F (Fintype.card V)).filter (fun S => d ≤ 4 * S.card)

theorem mem_paletteBadSets {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (d : ℕ) (S : Finset V) :
    S ∈ paletteBadSets F d ↔ 0 < S.card ∧ (F.induce (S : Set V)).Connected ∧ d ≤ 4 * S.card := by
  classical
  simp only [paletteBadSets, Finset.mem_filter, mem_smallConnectedSets]
  have hcard : S.card ≤ Fintype.card V := Finset.card_le_univ S
  tauto

theorem paletteBadSets_order_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d D u : ℕ) (hD : ∀ v, F.degree v ≤ D) :
    ((paletteBadSets F d).filter (fun S => S.card = u)).card ≤
      Fintype.card V * D ^ (2 * (u - 1)) := by
  classical
  apply (Finset.card_le_card ?_).trans (connectedSetsOfOrder_card_le F D u hD)
  intro S hS
  obtain ⟨hS, hcard⟩ := Finset.mem_filter.mp hS
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard, ((mem_paletteBadSets F d S).mp hS).2.1⟩

end Erdos911
