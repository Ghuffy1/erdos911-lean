import Erdos911.RetainedEdgeColoring
import Erdos911.BlockCapacity

namespace Erdos911

theorem retainedEdges_card_eq_filter {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (E : Finset (Sym2 W)) :
    (retainedEdges J E).card = (E.filter (fun e => e ∈ J.edgeSet)).card := by
  classical
  have hmap : (retainedEdges J E).map ⟨Subtype.val, Subtype.val_injective⟩ =
      E.filter (fun e => e ∈ J.edgeSet) := by
    ext e
    constructor
    · intro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
      exact Finset.mem_filter.mpr ⟨(mem_retainedEdges J E a).mp ha, a.property⟩
    · intro he
      obtain ⟨heE, heJ⟩ := Finset.mem_filter.mp he
      exact Finset.mem_map.mpr ⟨⟨e, heJ⟩, (mem_retainedEdges J E ⟨e, heJ⟩).mpr heE, rfl⟩
  rw [← hmap, Finset.card_map]

/-- Removing only edges incident to a specified host vertex set loses at
most the target maximum degree times the size of that host set in any copy. -/
theorem copy_retained_edges_lower_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : G.Copy H) (S : Finset W) (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ)
    (hkeep : ∀ u v, H.Adj u v → u ∉ S → v ∉ S → J.Adj u v) :
    G.edgeSet.ncard ≤ (retainedEdges J (copyRawEdges f)).card + S.card * Δ := by
  classical
  let T := copyVertexPreimage f S
  let lost := (copyRawEdges f).filter (fun e => e ∉ J.edgeSet)
  have hsubset : lost ⊆ (incidentEdgesAtSet G T).image (Sym2.map (f : V → W)) := by
    intro e he
    obtain ⟨hecopy, heJ⟩ := Finset.mem_filter.mp he
    obtain ⟨a, rfl⟩ := (mem_copyRawEdges_iff_exists f e).mp hecopy
    obtain ⟨a, ha⟩ := a
    induction a using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := ha
      have hnotadj : ¬J.Adj (f u) (f v) := heJ
      refine Finset.mem_image.mpr ⟨s(u, v), ?_, rfl⟩
      by_cases hu : f u ∈ S
      · apply Finset.mem_biUnion.mpr
        refine ⟨u, (mem_copyVertexPreimage f S u).mpr hu, ?_⟩
        rw [G.incidenceFinset_eq_filter]
        simp [huv]
      · have hv : f v ∈ S := by
          by_contra hv
          exact hnotadj (hkeep (f u) (f v) (map_rel f.toHom huv) hu hv)
        apply Finset.mem_biUnion.mpr
        refine ⟨v, (mem_copyVertexPreimage f S v).mpr hv, ?_⟩
        rw [G.incidenceFinset_eq_filter]
        simp [huv]
  have hlost : lost.card ≤ S.card * Δ := by
    calc
      lost.card ≤ ((incidentEdgesAtSet G T).image (Sym2.map (f : V → W))).card :=
        Finset.card_le_card hsubset
      _ ≤ (incidentEdgesAtSet G T).card := Finset.card_image_le
      _ ≤ T.card * Δ := incidentEdgesAtSet_card_le G T Δ hΔ
      _ ≤ S.card * Δ := Nat.mul_le_mul_right Δ (copyVertexPreimage_card_le f S)
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := copyRawEdges f) (fun e => e ∈ J.edgeSet)
  rw [← retainedEdges_card_eq_filter J (copyRawEdges f), copyRawEdges_card] at hsplit
  dsimp only [lost] at hlost
  omega

def degreePrunedGraph {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (D : ℕ) : SimpleGraph W where
  Adj u v := H.Adj u v ∧ H.degree u ≤ D ∧ H.degree v ≤ D
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _ h := H.irrefl h.1

instance {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ) :
    DecidableRel (degreePrunedGraph H D).Adj := by
  unfold degreePrunedGraph
  infer_instance

theorem degreePrunedGraph_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ) : degreePrunedGraph H D ≤ H :=
  fun _ _ h => h.1

theorem degreePrunedGraph_degree_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ) (v : W) :
    (degreePrunedGraph H D).degree v ≤ D := by
  by_cases hv : 0 < (degreePrunedGraph H D).degree v
  · obtain ⟨w, hw⟩ := ((degreePrunedGraph H D).degree_pos_iff_exists_adj v).mp hv
    exact ((SimpleGraph.Copy.ofLE _ _ (degreePrunedGraph_le H D)).degree_le v).trans hw.2.1
  · omega

theorem degreePruned_copy_retention {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (Δ D : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ) :
    (G.edgeSet.ncard : ℝ) ≤ (retainedEdges (degreePrunedGraph H D) (copyRawEdges f)).card +
      (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) := by
  classical
  let S := Finset.univ.filter (fun w => D < H.degree w)
  have hkeep : ∀ u v, H.Adj u v → u ∉ S → v ∉ S → (degreePrunedGraph H D).Adj u v := by
    intro u v huv hu hv
    have huD : H.degree u ≤ D := by simpa only [S, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt] using hu
    have hvD : H.degree v ≤ D := by simpa only [S, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt] using hv
    exact ⟨huv, huD, hvD⟩
  have hnat := copy_retained_edges_lower_bound G H (degreePrunedGraph H D) f S Δ hΔ hkeep
  have hreal : (G.edgeSet.ncard : ℝ) ≤
      (retainedEdges (degreePrunedGraph H D) (copyRawEdges f)).card + (S.card : ℝ) * Δ := by
    exact_mod_cast hnat
  have hS : (S.card : ℝ) ≤ 2 * H.edgeFinset.card / ((D + 1 : ℕ) : ℝ) := by
    simpa only [S, Nat.succ_le_iff] using high_degree_card_bound_real H (D + 1) (by omega)
  calc
    (G.edgeSet.ncard : ℝ) ≤
        (retainedEdges (degreePrunedGraph H D) (copyRawEdges f)).card + (S.card : ℝ) * Δ := hreal
    _ ≤ (retainedEdges (degreePrunedGraph H D) (copyRawEdges f)).card +
        (2 * H.edgeFinset.card / ((D + 1 : ℕ) : ℝ)) * Δ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hS (Nat.cast_nonneg Δ))
    _ = _ := by ring

end Erdos911
