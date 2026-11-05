import Erdos911.GraphForestBound
import Erdos911.GraphCounting

namespace Erdos911

/-- A finite graph has at most twice as many nonisolated vertices as edges. -/
theorem support_card_le_twice_edges {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    Fintype.card H.support ≤ 2 * H.edgeFinset.card := by
  classical
  have hfilter : Finset.univ.filter (fun w => 1 ≤ H.degree w) = H.support.toFinset := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      H.mem_support, ← H.degree_pos_iff_exists_adj w]
    omega
  have h := high_degree_card_bound H 1
  rw [hfilter, Nat.one_mul] at h
  simpa using h

/-- Copies of a target without isolated vertices restrict to the host support. -/
noncomputable def copyIntoSupport {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (hneighbors : ∀ v, ∃ w, G.Adj v w)
    (f : G.Copy H) : G.Copy (H.induce H.support) where
  toHom :=
    { toFun := fun v => ⟨f v, H.mem_support.mpr <| by
        obtain ⟨w, hw⟩ := hneighbors v
        exact ⟨f w, map_rel f.toHom hw⟩⟩
      map_rel' := fun hab => map_rel f.toHom hab }
  injective' := fun _ _ hab => f.injective (congrArg Subtype.val hab)

theorem copyIntoSupport_injective {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (hneighbors : ∀ v, ∃ w, G.Adj v w) :
    Function.Injective (copyIntoSupport G H hneighbors) := by
  intro f g h
  apply SimpleGraph.Copy.ext
  intro v
  exact congrArg Subtype.val (congrArg (fun c => c v) h)

/-- The forest bound expressed entirely in terms of the host edge count.
The source has no isolated vertices and contains an edge. -/
theorem graph_forest_copy_bound_edges {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v) :
    (Fintype.card (G.Copy H) : ℝ) ≤
      (2 * H.edgeFinset.card : ℝ) ^ Nat.card G.ConnectedComponent *
        ((2 * H.edgeFinset.card : ℝ) /
          ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ)) ^
          (Fintype.card V - Nat.card G.ConnectedComponent) *
            (D : ℝ) ^ (Fintype.card V - Nat.card G.ConnectedComponent) := by
  classical
  have hcopies : Fintype.card (G.Copy H) ≤
      Fintype.card (G.Copy (H.induce H.support)) :=
    Fintype.card_le_of_injective _ (copyIntoSupport_injective G H hneighbors)
  have hforest := graph_forest_copy_bound G (H.induce H.support) D hD hedge
  rw [H.card_edgeFinset_induce_support] at hforest
  have hsupport : (Fintype.card H.support : ℝ) ≤ 2 * H.edgeFinset.card := by
    exact_mod_cast support_card_le_twice_edges H
  have hroots := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Fintype.card H.support)
    hsupport (Nat.card G.ConnectedComponent)
  calc
    (Fintype.card (G.Copy H) : ℝ) ≤
        (Fintype.card (G.Copy (H.induce H.support)) : ℝ) := by exact_mod_cast hcopies
    _ ≤ _ := hforest
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hroots (by positivity)) (by positivity)

end Erdos911
