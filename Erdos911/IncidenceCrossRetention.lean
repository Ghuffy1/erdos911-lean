import Erdos911.IncidenceRetention
import Erdos911.DeletedEdgeCapacity

namespace Erdos911

/-- Only edges at actual high neighbors need to be preserved by the
auxiliary graph. Other missing edges do not contribute to the role's loss. -/
theorem copy_high_neighbor_loss_le_auxiliary {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J R : SimpleGraph W)
    [DecidableRel J.Adj] [DecidableRel R.Adj] (f : F.Copy H) (high : Finset W)
    (hkeep : ∀ v u, F.Adj v u → f u ∈ high → R.Adj (f v) (f u) → J.Adj (f v) (f u))
    (v : Fin n) :
    (copyHighNeighborLoss F H J f high v).card ≤ (F \ copyRetainedGraph R f).degree v := by
  apply Finset.card_le_card
  intro u hu
  obtain ⟨huU, huJ⟩ := Finset.mem_filter.mp hu
  obtain ⟨hFu, huHigh⟩ := (mem_copyHighNeighbors F f high v u).mp huU
  exact ((F \ copyRetainedGraph R f).mem_neighborFinset v u).mpr
    ⟨hFu, fun h => huJ (hkeep v u hFu huHigh h.2)⟩

theorem incidenceRetentionDefects_auxiliary_bound {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J R : SimpleGraph W)
    [DecidableRel J.Adj] [DecidableRel R.Adj] (f : F.Copy H)
    (right : Finset (Fin n)) (high : Finset W) (d : ℕ) (ε : ℝ)
    (hkeep : ∀ v u, F.Adj v u → f u ∈ high → R.Adj (f v) (f u) → J.Adj (f v) (f u)) :
    ε * d * (incidenceRetentionDefects F H J f right high d ε).card ≤
      4 * ((F \ copyRetainedGraph R f).edgeFinset.card : ℝ) := by
  classical
  let E := incidenceRetentionDefects F H J f right high d ε
  have hpoint (v : Fin n) (hv : v ∈ E) :
      ε * d / 2 ≤ ((F \ copyRetainedGraph R f).degree v : ℝ) := by
    have hloss := (Finset.mem_filter.mp hv).2
    have hdegree : ((copyHighNeighborLoss F H J f high v).card : ℝ) ≤
        (F \ copyRetainedGraph R f).degree v := by
      exact_mod_cast copy_high_neighbor_loss_le_auxiliary F H J R f high hkeep v
    exact hloss.le.trans hdegree
  have hsum : ε * d / 2 * E.card ≤ ∑ v, ((F \ copyRetainedGraph R f).degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ E, ε * d / 2 := by simp [mul_comm]
      _ ≤ ∑ v ∈ E, ((F \ copyRetainedGraph R f).degree v : ℝ) := Finset.sum_le_sum hpoint
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.cast_nonneg _)
  have htotal : (∑ v, ((F \ copyRetainedGraph R f).degree v : ℝ)) =
      2 * (F \ copyRetainedGraph R f).edgeFinset.card := by
    have h := (F \ copyRetainedGraph R f).sum_degrees_eq_twice_card_edges
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, SimpleGraph.edgeFinset_card,
      Set.fintypeCard_eq_ncard] using congrArg (Nat.cast : ℕ → ℝ) h
  rw [htotal] at hsum
  dsimp only [E] at hsum
  linarith only [hsum]

/-- The exception budget counts only the specified removed cross edges,
even when the candidate graph omits every low-low edge. -/
theorem incidenceRetentionDefects_cross_bound {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J K : SimpleGraph W)
    [DecidableRel J.Adj] [DecidableRel K.Adj] (T : ℕ)
    (hH : H ≤ lowEndpointPrunedGraph K T) (f : F.Copy H)
    (right : Finset (Fin n)) (B : Finset (Sym2 W)) (d : ℕ) (ε : ℝ)
    (hcross : ∀ x y, H.Adj x y → x ∉ highHostVertices K T → y ∈ highHostVertices K T →
      s(x, y) ∉ B → J.Adj x y) :
    ε * d * (incidenceRetentionDefects F H J f right (highHostVertices K T) d ε).card ≤
      4 * ((copyRawEdges f ∩ B).card : ℝ) := by
  classical
  let R := H.deleteEdges (B : Set (Sym2 W))
  have hkeep : ∀ v u, F.Adj v u → f u ∈ highHostVertices K T →
      R.Adj (f v) (f u) → J.Adj (f v) (f u) := by
    intro v u hFu huHigh hR
    have hlow := copy_low_of_high_neighbor F H K T hH f v u hFu huHigh
    have hR' := SimpleGraph.deleteEdges_adj.mp hR
    exact hcross (f v) (f u) hR'.1 hlow huHigh hR'.2
  have hbound := incidenceRetentionDefects_auxiliary_bound F H J R f right
    (highHostVertices K T) d ε hkeep
  have hmissing : (F \ copyRetainedGraph R f).edgeFinset.card ≤ (copyRawEdges f ∩ B).card :=
    copy_missing_edges_le R f B (fun _ _ hxy hB => SimpleGraph.deleteEdges_adj.mpr ⟨hxy, hB⟩)
  exact hbound.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hmissing) (by norm_num))

theorem incidenceRetentionDefects_cross_residual_bound {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel K.Adj] (T : ℕ)
    (hH : H ≤ lowEndpointPrunedGraph K T) (f : F.Copy H)
    (right : Finset (Fin n)) (B : Finset (Sym2 W)) (d : ℕ) (ε : ℝ) :
    ε * d * (incidenceRetentionDefects F H
      ((highLowGraph H (highHostVertices K T)).deleteEdges (B : Set (Sym2 W)))
      f right (highHostVertices K T) d ε).card ≤ 4 * ((copyRawEdges f ∩ B).card : ℝ) := by
  apply incidenceRetentionDefects_cross_bound F H _ K T hH f right B d ε
  intro x y hxy hx hy hB
  exact SimpleGraph.deleteEdges_adj.mpr ⟨⟨hxy, Or.inr ⟨hy, hx⟩⟩, hB⟩

end Erdos911
