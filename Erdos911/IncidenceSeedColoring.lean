import Erdos911.IncidenceRedExclusion

namespace Erdos911

/-- Candidate certificates and a shared avoidance of the list events
give an incidence coloring, with all blue costs measured in the original host. -/
theorem incidence_seed_marking_coloring {V U W I A : Type*}
    [Fintype V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (G : SimpleGraph U) [DecidableRel G.Adj]
    (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (hHK : H ≤ K) (hFG : F.IsContained G) (right : Finset U) (d TRight : ℕ) (Λ : ℝ)
    (hcover : G.IsVertexCover (right : Set U)) (hdegree : ∀ v ∈ right, G.degree v ≤ d)
    (hhost : (K.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hcutoff : 32 * Λ * d ≤ ((TRight + 1 : ℕ) : ℝ))
    (C : Finset A) (L : A → V → Finset W) (r h : ℕ) (T u initial prior budget : ℝ)
    (P : Finset (Sym2 W)) (B : I → Finset W)
    (hmarks : ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (L c.val) r T B h u) ∧
      (∑ e, if marks e = true then (B e.2).card * (d : ℝ) else 0) ≤ budget)
    (hcertificate : ∀ f : F.Copy H, Disjoint (copyRawEdges f) P → ∃ c ∈ C, ∃ E : Finset V,
      (E.card : ℝ) ≤ u ∧ (∀ v, (L c v).Nonempty → v ∉ E → f v ∈ L c v) ∧
      ∀ v, (L c v).Nonempty → v ∉ E → ∃ w, F.Adj v w ∧ f w ∈ highHostVertices K TRight)
    (hinitial : ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ initial)
    (hprior : ∀ f : G.Copy K, ((copyRawEdges f ∩ P).card : ℝ) ≤ prior)
    (hbudget : initial + prior + budget + (G.edgeSet.ncard : ℝ) / 16 < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  obtain ⟨marks, havoid, hcost⟩ := hmarks
  let high := highHostVertices K TRight
  let S := roundMarkedVertices B h marks
  let marked := rectangleEdges H S high
  let deleted := (K \ H).edgeFinset ∪ (P ∪ marked)
  have hredH : ¬F.IsContained (H.deleteEdges ((P ∪ marked : Finset (Sym2 W)) : Set (Sym2 W))) :=
    no_copy_of_cross_events_after_deletions F H J high C L r T u P B h marks havoid hcertificate
  have hkeep : K.deleteEdges (deleted : Set (Sym2 W)) ≤
      H.deleteEdges ((P ∪ marked : Finset (Sym2 W)) : Set (Sym2 W)) := by
    intro v w hvw
    obtain ⟨hK, hdeleted⟩ := SimpleGraph.deleteEdges_adj.mp hvw
    have hH : H.Adj v w := by
      by_contra hn
      exact hdeleted (Finset.mem_union_left _ (SimpleGraph.mem_edgeFinset.mpr ⟨hK, hn⟩))
    exact SimpleGraph.deleteEdges_adj.mpr
      ⟨hH, fun he => hdeleted (Finset.mem_union_right _ he)⟩
  have hred : ¬F.IsContained (K.deleteEdges (deleted : Set (Sym2 W))) :=
    fun hf => hredH (hf.trans ⟨SimpleGraph.Copy.ofLE _ _ hkeep⟩)
  have hcapacity (f : G.Copy K) : (copyRawEdges f ∩ deleted).card < G.edgeSet.ncard := by
    have hcross := incidence_cross_mark_budget G K f right d TRight Λ hcover hdegree hhost hcutoff
      (fun e : Fin h × I => B e.2) marks
    have hsub : copyRawEdges f ∩ marked ⊆ copyRawEdges f ∩ rectangleEdges K S high :=
      Finset.inter_subset_inter_left (rectangleEdges_mono hHK S high)
    have hcard : ((copyRawEdges f ∩ marked).card : ℝ) ≤
        (copyRawEdges f ∩ rectangleEdges K S high).card := by exact_mod_cast Finset.card_le_card hsub
    have hmarked : ((copyRawEdges f ∩ marked).card : ℝ) ≤ budget + (G.edgeSet.ncard : ℝ) / 16 := by
      have hcross' : ((copyRawEdges f ∩ rectangleEdges K S high).card : ℝ) ≤
          (∑ e, if marks e = true then (B e.2).card * (d : ℝ) else 0) + (G.edgeSet.ncard : ℝ) / 16 := hcross
      linarith only [hcard, hcross', hcost]
    have hpriorMarked : ((copyRawEdges f ∩ (P ∪ marked)).card : ℝ) ≤
        (copyRawEdges f ∩ P).card + (copyRawEdges f ∩ marked).card := by
      exact_mod_cast copy_capacity_union_inter (copyRawEdges f) P marked
    have htotal : ((copyRawEdges f ∩ deleted).card : ℝ) ≤
        (copyRawEdges f ∩ (K \ H).edgeFinset).card + (copyRawEdges f ∩ (P ∪ marked)).card := by
      exact_mod_cast copy_capacity_union_inter (copyRawEdges f) (K \ H).edgeFinset (P ∪ marked)
    have hlt : ((copyRawEdges f ∩ deleted).card : ℝ) < G.edgeSet.ncard := by
      linarith only [htotal, hpriorMarked, hmarked, hinitial f, hprior f, hbudget]
    exact_mod_cast hlt
  exact avoiding_coloring_of_deleted_capacity F G K hFG deleted hred hcapacity

end Erdos911
