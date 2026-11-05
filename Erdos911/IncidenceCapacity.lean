import Erdos911.HighLowHost
import Erdos911.MarkedNeighborhoodStars
import Erdos911.HostPruningComposition

namespace Erdos911

/-- A selected family of copy edges can be charged to target roles whose
degrees have a local bound. Only their host images enter the vertex count. -/
theorem copy_role_cover_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (f : G.Copy H) (right : Finset V) (S : Finset W) (E : Finset (Sym2 W)) (d : ℕ)
    (hdegree : ∀ v ∈ right, G.degree v ≤ d)
    (hcover : ∀ u v, G.Adj u v → s(f u, f v) ∈ E →
      (u ∈ right ∧ f u ∈ S) ∨ (v ∈ right ∧ f v ∈ S)) :
    (copyRawEdges f ∩ E).card ≤ S.card * d := by
  classical
  let T := right ∩ copyVertexPreimage f S
  have hsub : copyRawEdges f ∩ E ⊆ (incidentEdgesAtSet G T).image (Sym2.map (f : V → W)) := by
    intro e he
    obtain ⟨heCopy, heE⟩ := Finset.mem_inter.mp he
    obtain ⟨a, hae⟩ := (mem_copyRawEdges_iff_exists f e).mp heCopy
    obtain ⟨a, ha⟩ := a
    induction a using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := ha
      have hE : s(f u, f v) ∈ E := by
        change Sym2.map (f : V → W) s(u, v) ∈ E
        rwa [hae]
      apply Finset.mem_image.mpr
      refine ⟨s(u, v), ?_, hae⟩
      apply (mem_incidentEdgesAtSet_iff G T _).mpr
      refine ⟨G.mem_edgeFinset.mpr huv, ?_⟩
      rcases hcover u v huv hE with ⟨huR, huS⟩ | ⟨hvR, hvS⟩
      · exact ⟨u, Finset.mem_inter.mpr ⟨huR, (mem_copyVertexPreimage f S u).mpr huS⟩, by simp⟩
      · exact ⟨v, Finset.mem_inter.mpr ⟨hvR, (mem_copyVertexPreimage f S v).mpr hvS⟩, by simp⟩
  calc
    _ ≤ ((incidentEdgesAtSet G T).image (Sym2.map (f : V → W))).card := Finset.card_le_card hsub
    _ ≤ (incidentEdgesAtSet G T).card := Finset.card_image_le
    _ ≤ T.card * d := incidentEdgesAtSet_card_le_on G T d
      (fun v hv => hdegree v (Finset.mem_inter.mp hv).1)
    _ ≤ S.card * d := Nat.mul_le_mul_right d
      ((Finset.card_le_card Finset.inter_subset_right).trans (copyVertexPreimage_card_le f S))

theorem copy_rectangle_capacity_from_cover {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (f : G.Copy H) (right : Finset V) (S high : Finset W) (d : ℕ)
    (hcover : G.IsVertexCover (right : Set V)) (hdegree : ∀ v ∈ right, G.degree v ≤ d) :
    (copyRawEdges f ∩ rectangleEdges H S high).card ≤ S.card * d + high.card * d := by
  have h := copy_role_cover_capacity G H f right (S ∪ high) (rectangleEdges H S high) d hdegree (by
    intro u v huv he
    have hends := rectangleEdges_endpoints H S high he
    exact (hcover huv).imp (fun hu => ⟨hu, hends.1⟩) (fun hv => ⟨hv, hends.2⟩))
  exact h.trans (by
    have hc := Nat.mul_le_mul_right d (Finset.card_union_le S high)
    simpa only [Nat.add_mul] using hc)

theorem copy_high_high_capacity_from_cover {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (right : Finset V) (d T : ℕ)
    (hcover : G.IsVertexCover (right : Set V)) (hdegree : ∀ v ∈ right, G.degree v ≤ d) :
    (copyRawEdges f ∩ (H \ lowEndpointPrunedGraph H T).edgeFinset).card ≤
      (highHostVertices H T).card * d := by
  apply copy_role_cover_capacity G H f right (highHostVertices H T) _ d hdegree
  intro u v huv he
  have hdeleted := SimpleGraph.mem_edgeFinset.mp he
  have hnot : ¬(H.degree (f u) ≤ T ∨ H.degree (f v) ≤ T) := by
    intro hlow
    exact hdeleted.2 ⟨map_rel f.toHom huv, hlow⟩
  have huHigh : f u ∈ highHostVertices H T :=
    (mem_highHostVertices H T (f u)).mpr (Nat.lt_of_not_ge (fun hu => hnot (Or.inl hu)))
  have hvHigh : f v ∈ highHostVertices H T :=
    (mem_highHostVertices H T (f v)).mpr (Nat.lt_of_not_ge (fun hv => hnot (Or.inr hv)))
  exact (hcover huv).imp (fun hu => ⟨hu, huHigh⟩) (fun hv => ⟨hv, hvHigh⟩)

theorem markedVertexUnion_card_le {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (marks : I → Bool) :
    (markedVertexUnion B marks).card ≤ ∑ i, if marks i = true then (B i).card else 0 := by
  classical
  simpa only [markedVertexUnion, Finset.sum_filter] using
    (Finset.card_biUnion_le (s := Finset.univ.filter (fun i => marks i = true)) (t := B))

/-- The high-image allowance is charged once for the union of all marks. -/
theorem copy_marked_rectangle_capacity {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) (f : G.Copy H)
    (right : Finset V) (high : Finset W) (d : ℕ)
    (hcover : G.IsVertexCover (right : Set V)) (hdegree : ∀ v ∈ right, G.degree v ≤ d)
    (B : I → Finset W) (marks : I → Bool) :
    ((copyRawEdges f ∩ rectangleEdges H (markedVertexUnion B marks) high).card : ℝ) ≤
      (∑ i, if marks i = true then (B i).card * (d : ℝ) else 0) + high.card * (d : ℝ) := by
  classical
  have hcap : ((copyRawEdges f ∩ rectangleEdges H (markedVertexUnion B marks) high).card : ℝ) ≤
      (markedVertexUnion B marks).card * (d : ℝ) + high.card * (d : ℝ) := by
    exact_mod_cast copy_rectangle_capacity_from_cover G H f right _ high d hcover hdegree
  have hcard : ((markedVertexUnion B marks).card : ℝ) ≤
      ∑ i, if marks i = true then ((B i).card : ℝ) else 0 := by
    exact_mod_cast markedVertexUnion_card_le B marks
  have hweighted := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg (α := ℝ) d)
  rw [Finset.sum_mul] at hweighted
  simp only [ite_mul, zero_mul] at hweighted
  exact hcap.trans (add_le_add hweighted le_rfl)

theorem high_host_right_capacity_bound {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (d T : ℕ) (Λ E : ℝ)
    (hE : 0 ≤ E) (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * E)
    (hcutoff : 32 * Λ * d ≤ ((T + 1 : ℕ) : ℝ)) :
    ((highHostVertices H T).card : ℝ) * d ≤ E / 16 := by
  calc
    _ ≤ (2 * H.edgeFinset.card / ((T + 1 : ℕ) : ℝ)) * d :=
      mul_le_mul_of_nonneg_right (highHostVertices_card_bound H T) (Nat.cast_nonneg d)
    _ = 2 * (d : ℝ) * H.edgeFinset.card / ((T + 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := pruning_fraction_bound E H.edgeFinset.card Λ d T hE (Nat.cast_nonneg d) hhost hcutoff

theorem incidence_cross_mark_budget {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (right : Finset V) (d T : ℕ) (Λ : ℝ)
    (hcover : G.IsVertexCover (right : Set V)) (hdegree : ∀ v ∈ right, G.degree v ≤ d)
    (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hcutoff : 32 * Λ * d ≤ ((T + 1 : ℕ) : ℝ))
    (B : I → Finset W) (marks : I → Bool) :
    ((copyRawEdges f ∩ rectangleEdges H (markedVertexUnion B marks) (highHostVertices H T)).card : ℝ) ≤
      (∑ i, if marks i = true then (B i).card * (d : ℝ) else 0) + (G.edgeSet.ncard : ℝ) / 16 := by
  exact (copy_marked_rectangle_capacity G H f right (highHostVertices H T) d hcover hdegree B marks).trans
    (add_le_add le_rfl (high_host_right_capacity_bound H d T Λ G.edgeSet.ncard (Nat.cast_nonneg _) hhost hcutoff))

theorem incidence_high_high_pruning_budget {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (right : Finset V) (d T : ℕ) (Λ : ℝ)
    (hcover : G.IsVertexCover (right : Set V)) (hdegree : ∀ v ∈ right, G.degree v ≤ d)
    (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hcutoff : 32 * Λ * d ≤ ((T + 1 : ℕ) : ℝ)) :
    ((copyRawEdges f ∩ (H \ lowEndpointPrunedGraph H T).edgeFinset).card : ℝ) ≤
      (G.edgeSet.ncard : ℝ) / 16 := by
  have hcap : ((copyRawEdges f ∩ (H \ lowEndpointPrunedGraph H T).edgeFinset).card : ℝ) ≤
      (highHostVertices H T).card * (d : ℝ) := by
    exact_mod_cast copy_high_high_capacity_from_cover G H f right d T hcover hdegree
  exact hcap.trans (high_host_right_capacity_bound H d T Λ G.edgeSet.ncard (Nat.cast_nonneg _) hhost hcutoff)

end Erdos911
