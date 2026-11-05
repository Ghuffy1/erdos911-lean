import Erdos911.DegreePeeling
import Erdos911.DyadicBudget

namespace Erdos911

def indexedEdgeGraph {V : Type*} (G : SimpleGraph V) (index : Sym2 V → ℕ) (j : ℕ) :
    SimpleGraph V := G.deleteEdges {e | index e ≠ j}

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (index : Sym2 V → ℕ) (j : ℕ) :
    DecidableRel (indexedEdgeGraph G index j).Adj := by
  unfold indexedEdgeGraph
  infer_instance

theorem indexedEdgeGraph_adj {V : Type*} (G : SimpleGraph V) (index : Sym2 V → ℕ)
    (j : ℕ) (u v : V) : (indexedEdgeGraph G index j).Adj u v ↔ G.Adj u v ∧ index s(u, v) = j := by
  simp only [indexedEdgeGraph, SimpleGraph.deleteEdges_adj, Set.mem_ofPred_eq, not_not]

theorem indexedEdgeGraph_le {V : Type*} (G : SimpleGraph V) (index : Sym2 V → ℕ) (j : ℕ) :
    indexedEdgeGraph G index j ≤ G := G.deleteEdges_le _

theorem indexedEdgeGraph_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (index : Sym2 V → ℕ) (j : ℕ) :
    (indexedEdgeGraph G index j).edgeFinset = G.edgeFinset.filter (fun e => index e = j) := by
  classical
  ext e
  rw [Finset.mem_filter]
  constructor
  · intro he
    have hs := (indexedEdgeGraph G index j).mem_edgeFinset.mp he
    change e ∈ (G.deleteEdges {e | index e ≠ j}).edgeSet at hs
    rw [G.edgeSet_deleteEdges] at hs
    exact ⟨G.mem_edgeFinset.mpr hs.1, not_not.mp hs.2⟩
  · rintro ⟨he, hj⟩
    apply (indexedEdgeGraph G index j).mem_edgeFinset.mpr
    change e ∈ (G.deleteEdges {e | index e ≠ j}).edgeSet
    rw [G.edgeSet_deleteEdges]
    exact ⟨G.mem_edgeFinset.mp he, not_not.mpr hj⟩

theorem indexedEdgeGraph_edge_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (index : Sym2 V → ℕ) (N : ℕ)
    (hindex : ∀ e ∈ G.edgeFinset, index e < N) :
    (∑ j : Fin N, (indexedEdgeGraph G index j.val).edgeSet.ncard) = G.edgeSet.ncard := by
  classical
  simp_rw [← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card]
  simp_rw [indexedEdgeGraph_edgeFinset, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hi := hindex e he
  have heq (j : Fin N) : index e = j.val ↔ j = ⟨index e, hi⟩ := by
    constructor
    · intro h
      apply Fin.ext
      exact h.symm
    · rintro rfl
      rfl
  simp only [heq]
  simp

def edgeMinWeight {V : Type*} (w : V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => min (w u) (w v), fun _ _ => min_comm _ _⟩

@[simp] theorem edgeMinWeight_mk {V : Type*} (w : V → ℕ) (u v : V) :
    edgeMinWeight w s(u, v) = min (w u) (w v) := rfl

def dyadicEdgeBand {V : Type*} (G : SimpleGraph V) (w : V → ℕ) (j : ℕ) : SimpleGraph V :=
  indexedEdgeGraph G (fun e => Nat.log 2 (edgeMinWeight w e)) j

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ) (j : ℕ) :
    DecidableRel (dyadicEdgeBand G w j).Adj := by unfold dyadicEdgeBand; infer_instance

theorem dyadicEdgeBand_le {V : Type*} (G : SimpleGraph V) (w : V → ℕ) (j : ℕ) :
    dyadicEdgeBand G w j ≤ G := indexedEdgeGraph_le G _ j

theorem dyadicEdgeBand_adj {V : Type*} (G : SimpleGraph V) (w : V → ℕ) (j : ℕ) (u v : V) :
    (dyadicEdgeBand G w j).Adj u v ↔ G.Adj u v ∧ Nat.log 2 (min (w u) (w v)) = j := by
  simp only [dyadicEdgeBand, indexedEdgeGraph_adj, edgeMinWeight_mk]

theorem dyadicEdgeBand_weight_bounds {V : Type*} (G : SimpleGraph V) (w : V → ℕ)
    (j : ℕ) (u v : V) (hadj : (dyadicEdgeBand G w j).Adj u v)
    (hpos : 0 < min (w u) (w v)) :
    2 ^ j ≤ min (w u) (w v) ∧ min (w u) (w v) < 2 * 2 ^ j := by
  obtain ⟨_, hj⟩ := (dyadicEdgeBand_adj G w j u v).mp hadj
  simpa only [dyadicFloor, hj] using dyadicFloor_bounds (min (w u) (w v)) hpos

theorem dyadicEdgeBand_support_lower {V : Type*} (G : SimpleGraph V) (w : V → ℕ)
    (hpos : ∀ u v, G.Adj u v → 0 < min (w u) (w v)) (j : ℕ) (v : V)
    (hv : v ∈ (dyadicEdgeBand G w j).support) : 2 ^ j ≤ w v := by
  obtain ⟨u, hvu⟩ := hv
  have hG := ((dyadicEdgeBand_adj G w j v u).mp hvu).1
  exact ((dyadicEdgeBand_weight_bounds G w j v u hvu (hpos v u hG)).1).trans (min_le_left _ _)

theorem dyadicEdgeBand_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ) (M : ℕ) (hM : ∀ v, w v ≤ M) :
    (∑ j : Fin (Nat.log 2 M + 1), (dyadicEdgeBand G w j.val).edgeSet.ncard) = G.edgeSet.ncard := by
  apply indexedEdgeGraph_edge_partition
  intro e _
  have hw : edgeMinWeight w e ≤ M := by
    induction e using Sym2.inductionOn with
    | hf u v => exact (min_le_left _ _).trans (hM u)
  have h := Nat.log_mono_right (b := 2) hw
  omega

theorem dyadicEdgeBand_minimum_scale {V : Type*} [Fintype V]
    (G : SimpleGraph V) (w : V → ℕ) (j d : ℕ) (hmin : ∀ v, d ≤ w v)
    (hpos : ∀ u v, G.Adj u v → 0 < min (w u) (w v))
    (hedge : 0 < (dyadicEdgeBand G w j).edgeSet.ncard) : d < 2 * 2 ^ j := by
  classical
  obtain ⟨e, he⟩ := (Set.ncard_pos (s := (dyadicEdgeBand G w j).edgeSet)).mp hedge
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hG := (dyadicEdgeBand_le G w j) he
    have h := (dyadicEdgeBand_weight_bounds G w j u v he (hpos u v hG)).2
    exact (le_min (hmin u) (hmin v)).trans_lt h

end Erdos911
