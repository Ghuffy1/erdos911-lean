import Erdos911.HighHighPruning

namespace Erdos911

noncomputable def highHostVertices {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) : Finset W := by
  classical
  exact Finset.univ.filter (fun x => T < H.degree x)

theorem mem_highHostVertices {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) (x : W) :
    x ∈ highHostVertices H T ↔ T < H.degree x := by
  classical
  simp only [highHostVertices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem highHostVertices_card_bound {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) :
    ((highHostVertices H T).card : ℝ) ≤ 2 * H.edgeFinset.card / ((T + 1 : ℕ) : ℝ) := by
  simpa only [highHostVertices, Nat.succ_le_iff] using high_degree_card_bound_real H (T + 1) (by omega)

/-- The partition is fixed independently of subsequent edge deletions. -/
def highLowGraph {W : Type*} [DecidableEq W] (H : SimpleGraph W) (high : Finset W) : SimpleGraph W where
  Adj u v := H.Adj u v ∧ ((u ∈ high ∧ v ∉ high) ∨ (v ∈ high ∧ u ∉ high))
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := H.irrefl h.1

instance {W : Type*} [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] (high : Finset W) :
    DecidableRel (highLowGraph H high).Adj := by
  unfold highLowGraph
  infer_instance

theorem highLowGraph_le {W : Type*} [DecidableEq W] (H : SimpleGraph W) (high : Finset W) :
    highLowGraph H high ≤ H := fun _ _ h => h.1

theorem highLowGraph_mono {W : Type*} [DecidableEq W] {H J : SimpleGraph W}
    (hHJ : H ≤ J) (high : Finset W) : highLowGraph H high ≤ highLowGraph J high :=
  fun _ _ h => ⟨hHJ h.1, h.2⟩

theorem highLowGraph_low_degree {W : Type*} [Fintype W] [DecidableEq W]
    (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (T : ℕ) (x : W) (hx : x ∉ highHostVertices K T) :
    (highLowGraph H (highHostVertices K T)).degree x ≤ T := by
  have hdegree := (SimpleGraph.Copy.ofLE (highLowGraph H (highHostVertices K T)) K
    ((highLowGraph_le H (highHostVertices K T)).trans hHK)).degree_le x
  have hx' : K.degree x ≤ T := Nat.le_of_not_gt (fun h => hx ((mem_highHostVertices K T x).mpr h))
  exact hdegree.trans hx'

theorem highLowGraph_low_neighbor_high {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (high : Finset W) {x y : W}
    (hx : x ∉ high) (hxy : (highLowGraph H high).Adj x y) : y ∈ high := by
  rcases hxy.2 with h | h
  · exact (hx h.1).elim
  · exact h.1

end Erdos911
