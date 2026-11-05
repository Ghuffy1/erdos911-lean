import Erdos911.DenseCorePacking
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace Erdos911

def corePackingGraph {V : Type*} (G : SimpleGraph V) (P : Finset (Finset V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∃ T ∈ P, u ∈ T ∧ v ∈ T
  symm.symm u v h := ⟨h.1.symm, by
    obtain ⟨T, hT, hu, hv⟩ := h.2
    exact ⟨T, hT, hv, hu⟩⟩
  loopless.irrefl v h := G.loopless.irrefl v h.1

theorem corePackingGraph_le {V : Type*} (G : SimpleGraph V) (P : Finset (Finset V)) :
    corePackingGraph G P ≤ G := fun _ _ h => h.1

def corePackingPartCopy {V : Type*} (G : SimpleGraph V) (P : Finset (Finset V))
    (T : Finset V) (hT : T ∈ P) : (G.induce (T : Set V)).Copy (corePackingGraph G P) where
  toHom := {
    toFun := Subtype.val
    map_rel' := fun h => ⟨h, T, hT, Subtype.property _, Subtype.property _⟩
  }
  injective' := Subtype.val_injective

theorem corePackingGraph_support {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) :
    (corePackingGraph G P).support ⊆ (P.biUnion id : Set V) := by
  intro v hv
  obtain ⟨w, hw⟩ := hv
  obtain ⟨T, hT, hvT, _⟩ := hw.2
  exact Finset.mem_biUnion.mpr ⟨T, hT, hvT⟩

theorem corePackingGraph_degree_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K s : ℕ) (P : Finset (Finset V))
    (hP : DegreeCoreFamily G K s P) (v : V) (hv : v ∈ P.biUnion id) :
    letI : DecidableRel (corePackingGraph G P).Adj := Classical.decRel _
    s ≤ (corePackingGraph G P).degree v := by
  classical
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hv
  have h := (hP.2 T hT).2.2 ⟨v, hvT⟩
  have hdeg := (corePackingPartCopy G P T hT).degree_le ⟨v, hvT⟩
  have h' : s ≤ (G.induce (T : Set V)).degree ⟨v, hvT⟩ := by
    simpa only [SimpleGraph.ncard_neighborSet] using h
  exact h'.trans hdeg

theorem corePackingGraph_edge_mass {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K s : ℕ) (P : Finset (Finset V))
    (hP : DegreeCoreFamily G K s P) :
    (s : ℝ) * (P.biUnion id).card ≤ 2 * (corePackingGraph G P).edgeSet.ncard := by
  classical
  let J := corePackingGraph G P
  calc
    _ = ∑ _v ∈ P.biUnion id, (s : ℝ) := by simp [mul_comm]
    _ ≤ ∑ v ∈ P.biUnion id, (J.degree v : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact_mod_cast corePackingGraph_degree_lower G K s P hP v hv
    _ ≤ ∑ v, (J.degree v : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun v _ _ => Nat.cast_nonneg _)
    _ = _ := by
      have h := J.sum_degrees_eq_twice_card_edges
      rw [J.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
      exact_mod_cast h

theorem corePackingGraph_adj_same_part {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K s : ℕ) (P : Finset (Finset V))
    (hP : DegreeCoreFamily G K s P) (T : Finset V) (hT : T ∈ P)
    {u v : V} (hu : u ∈ T) (huv : (corePackingGraph G P).Adj u v) : v ∈ T := by
  obtain ⟨A, hA, huA, hvA⟩ := huv.2
  by_cases hAT : A = T
  · simpa only [hAT] using hvA
  · exact (Finset.disjoint_left.mp (hP.1 A hA T hT hAT) huA hu).elim

theorem corePackingGraph_reachable_same_part {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K s : ℕ) (P : Finset (Finset V))
    (hP : DegreeCoreFamily G K s P) (T : Finset V) (hT : T ∈ P)
    {u v : V} (hu : u ∈ T) (huv : (corePackingGraph G P).Reachable u v) : v ∈ T := by
  obtain ⟨p⟩ := huv
  revert hu
  induction p with
  | nil => exact id
  | cons h p ih =>
    intro hu
    exact ih (corePackingGraph_adj_same_part G K s P hP T hT hu h)

/-- Restricting the packed graph to its chosen vertices removes only
isolates. Every connected component stays inside one chosen small core. -/
theorem corePackingGraph_component_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K s : ℕ) (P : Finset (Finset V))
    (hP : DegreeCoreFamily G K s P)
    (c : ((corePackingGraph G P).induce (P.biUnion id : Set V)).ConnectedComponent) :
    Nat.card c.supp ≤ K := by
  classical
  let J := corePackingGraph G P
  let W := J.induce (P.biUnion id : Set V)
  obtain ⟨v, hv⟩ := c.nonempty_supp
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp v.property
  have hmem (w : c.supp) : w.val.val ∈ T := by
    have hr := (c.reachable_of_mem_supp hv w.property).map
      (SimpleGraph.Copy.induce J (P.biUnion id : Set V)).toHom
    exact corePackingGraph_reachable_same_part G K s P hP T hT hvT hr
  let f : c.supp → ↥T := fun w => ⟨w.val.val, hmem w⟩
  have hf : Function.Injective f := by
    intro u w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : ↥T => x.val) h
  have hcard := Nat.card_le_card_of_injective f hf
  have hcard' : Nat.card c.supp ≤ T.card := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
  exact hcard'.trans (hP.2 T hT).2.1

end Erdos911
