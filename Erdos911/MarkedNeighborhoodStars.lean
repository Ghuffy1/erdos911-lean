import Erdos911.BlockedListEvents
import Erdos911.HostDegreePruning

namespace Erdos911

noncomputable def roundMarkedVertices {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (marks : (Fin h × I) → Bool) : Finset W :=
  markedVertexUnion (fun x : Fin h × I => B x.2) marks

theorem mem_roundMarkedVertices {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (marks : (Fin h × I) → Bool) (x : W) :
    x ∈ roundMarkedVertices B h marks ↔ ∃ r i, marks (r, i) = true ∧ x ∈ B i := by
  rw [roundMarkedVertices, mem_markedVertexUnion]
  simp only [Prod.exists]

theorem run_uncovered_membership {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) : ∀ (h : ℕ) (L : Finset W) (marks : Fin h → I → Bool) (x : W),
      x ∈ runRounds (uncoveredVertices B) L marks ↔
        x ∈ L ∧ ∀ r, x ∉ markedVertexUnion B (marks r) := by
  intro h
  induction h with
  | zero => intros; simp [runRounds]
  | succ h ih =>
    intro L marks x
    simp only [runRounds, ih, uncoveredVertices, Finset.mem_sdiff, Fin.forall_fin_succ, and_assoc]

theorem run_uncovered_eq_sdiff_roundMarked {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : Finset W) (marks : (Fin h × I) → Bool) :
    runRounds (uncoveredVertices B) L (fun r i => marks (r, i)) = L \ roundMarkedVertices B h marks := by
  classical
  ext x
  rw [run_uncovered_membership, Finset.mem_sdiff, mem_roundMarkedVertices]
  simp only [mem_markedVertexUnion, not_exists]

theorem listBlocked_iff_subset_roundMarked {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : Finset W) (marks : (Fin h × I) → Bool) :
    marks ∈ listBlocked B h L ↔ L ⊆ roundMarkedVertices B h marks := by
  change runRounds (uncoveredVertices B) L (fun r i => marks (r, i)) = ∅ ↔ _
  rw [run_uncovered_eq_sdiff_roundMarked, Finset.sdiff_eq_empty_iff_subset]

theorem mem_incidentEdgesAtSet_iff {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) (e : Sym2 W) :
    e ∈ incidentEdgesAtSet H S ↔ e ∈ H.edgeFinset ∧ ∃ x ∈ S, x ∈ e := by
  simp only [incidentEdgesAtSet, Finset.mem_biUnion, H.incidenceFinset_eq_filter, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, he, hxe⟩
    exact ⟨he, x, hx, hxe⟩
  · rintro ⟨he, x, hx, hxe⟩
    exact ⟨x, hx, he, hxe⟩

theorem adjacent_marked_edge {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) (u v : W)
    (huv : H.Adj u v) (hu : u ∈ S) : s(u, v) ∈ incidentEdgesAtSet H S := by
  apply (mem_incidentEdgesAtSet_iff H S _).mpr
  exact ⟨H.mem_edgeFinset.mpr huv, u, hu, by simp⟩

/-- A star mark at a host vertex has capacity at most the maximum target
degree, even when several marked stars overlap. -/
theorem copy_incident_vertex_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (S : Finset W) (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ) :
    (copyRawEdges f ∩ incidentEdgesAtSet H S).card ≤ S.card * Δ := by
  classical
  let T := copyVertexPreimage f S
  have hsub : copyRawEdges f ∩ incidentEdgesAtSet H S ⊆
      (incidentEdgesAtSet G T).image (Sym2.map (f : V → W)) := by
    intro e he
    obtain ⟨a, hae⟩ := (mem_copyRawEdges_iff_exists f e).mp (Finset.mem_inter.mp he).1
    obtain ⟨a, ha⟩ := a
    induction a using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := ha
      have hincident := (mem_incidentEdgesAtSet_iff H S e).mp (Finset.mem_inter.mp he).2
      obtain ⟨w, hw, hwe⟩ := hincident.2
      have hwuv : w = f u ∨ w = f v := by
        rw [← hae] at hwe
        simpa only [Sym2.map_mk, Sym2.mem_iff] using hwe
      apply Finset.mem_image.mpr
      refine ⟨s(u, v), ?_, hae⟩
      apply (mem_incidentEdgesAtSet_iff G T _).mpr
      refine ⟨G.mem_edgeFinset.mpr huv, ?_⟩
      rcases hwuv with rfl | rfl
      · exact ⟨u, (mem_copyVertexPreimage f S u).mpr hw, by simp⟩
      · exact ⟨v, (mem_copyVertexPreimage f S v).mpr hw, by simp⟩
  calc
    _ ≤ ((incidentEdgesAtSet G T).image (Sym2.map (f : V → W))).card := Finset.card_le_card hsub
    _ ≤ (incidentEdgesAtSet G T).card := Finset.card_image_le
    _ ≤ T.card * Δ := incidentEdgesAtSet_card_le G T Δ hΔ
    _ ≤ S.card * Δ := Nat.mul_le_mul_right Δ (copyVertexPreimage_card_le f S)

theorem markedVertexUnion_copy_capacity {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (B : I → Finset W) (marks : I → Bool) (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ) :
    ((copyRawEdges f ∩ incidentEdgesAtSet H (markedVertexUnion B marks)).card : ℝ) ≤
      ∑ i, if marks i = true then (B i).card * (Δ : ℝ) else 0 := by
  classical
  let marked := Finset.univ.filter (fun i => marks i = true)
  have heq : copyRawEdges f ∩ incidentEdgesAtSet H (markedVertexUnion B marks) =
      marked.biUnion (fun i => copyRawEdges f ∩ incidentEdgesAtSet H (B i)) := by
    ext e
    simp only [Finset.mem_inter, mem_incidentEdgesAtSet_iff, mem_markedVertexUnion,
      marked, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  calc
    _ = ((marked.biUnion (fun i => copyRawEdges f ∩ incidentEdgesAtSet H (B i))).card : ℝ) := by rw [heq]
    _ ≤ ∑ i ∈ marked, ((copyRawEdges f ∩ incidentEdgesAtSet H (B i)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ i ∈ marked, (B i).card * (Δ : ℝ) := Finset.sum_le_sum (fun i _ => by
      exact_mod_cast copy_incident_vertex_capacity G H f (B i) Δ hΔ)
    _ = _ := by simp only [marked, Finset.sum_filter]

end Erdos911
