import Erdos911.IncidenceRelabeling

namespace Erdos911

/-- Relabelling a component preserves its right roles, exact edge count,
and orientation exceptions in the incidence coloring criterion. -/
theorem incidence_coloring_after_pruning_general (A : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V U W : Type*)
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ D P : ℕ, d ≤ P →
    ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U) [DecidableRel G.Adj]
      (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj],
    F.Connected → F.IsContained G → H ≤ lowEndpointPrunedGraph K P → J ≤ H →
    (∀ v, d ≤ F.degree v) → (∀ v, F.degree v ≤ D) → D ≤ d ^ A →
    (∀ w, H.degree w ≤ D) → 0 < G.edgeSet.ncard →
    ∀ (rightF : Finset V) (rightG : Finset U),
    (∀ v ∈ rightF, F.degree v ≤ d) → F.edgeSet.ncard = d * rightF.card →
    Fintype.card V ≤ 2 * rightF.card →
    G.IsVertexCover (rightG : Set U) → (∀ v ∈ rightG, G.degree v ≤ d) →
    (∀ X Y : Finset W, X.card = baselineBlockSize d → Y.card = baselineBlockSize d →
      Disjoint X Y → (crossEdges J X Y : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) →
    (∀ X Y : Finset W, X.card = nearRegularBlockSize d → Y.card = nearRegularBlockSize d →
      Disjoint X Y → (crossEdges J X Y : ℝ) ≤
        nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) →
    ∀ (Λ : ℝ) (prior removed : Finset (Sym2 W)), 1 ≤ Λ →
    (K.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard → 32 * Λ * d ≤ (P : ℝ) →
    (∀ x y, H.Adj x y → x ∉ highHostVertices K P → y ∈ highHostVertices K P →
      s(x, y) ∉ removed → J.Adj x y) →
    (∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4) →
    (∀ f : G.Copy K, ((copyRawEdges f ∩ prior).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 2) →
    (∀ f : F.Copy H, Disjoint (copyRawEdges f) prior →
      ((copyRawEdges f ∩ removed).card : ℝ) ≤ nearRegularLossFraction B d * F.edgeSet.ncard) →
    (∀ f : F.Copy H, Disjoint (copyRawEdges f) prior →
      (d : ℝ) * (incidenceOrientationDefects F f rightF (highHostVertices K P) d).card ≤
        (F.edgeSet.ncard : ℝ) / 32) →
    (∀ f : F.Copy H, Disjoint (copyRawEdges f) prior →
      copyRawEdges f ∉ starImagePatterns H J (copyVertices f) (tolerantTupleOrder d)
        F.edgeSet.ncard D P ((F.edgeSet.ncard : ℝ) / 128 *
          Real.log ((P : ℝ) / incidenceCommonCutoff A P d))) →
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  obtain ⟨d₀, hd₀⟩ := incidence_coloring_after_pruning A B hB
  refine ⟨d₀, ?_⟩
  intro d hd V U W _ _ _ _ _ _ D P hdP F _ G _ K H J _ _ _ hF hFG hH hJ hmin hmax hDpow hhost hGpos
    rightF rightG hrightF hbalance hhalf hcover hrightG hfirst hsecond Λ prior removed hΛ hKedges hcutoff
    hcross hinitial hprior hloss horient hgood
  classical
  let vertexEquiv := (Fintype.equivFin V).symm
  let F' := F.comap vertexEquiv
  let e : F' ≃g F := SimpleGraph.Iso.comap vertexEquiv F
  let rightF' := rightF.image e.symm
  have hrightCard : rightF'.card = rightF.card := Finset.card_image_of_injective _ e.symm.injective
  have hF' : F'.Connected := e.connected_iff.mpr hF
  have hFG' : F'.IsContained G := (show F'.IsContained F from ⟨e.toCopy⟩).trans hFG
  have hmin' : ∀ v, d ≤ F'.degree v := by
    intro v
    rw [← e.degree_eq v]
    exact hmin (e v)
  have hmax' : ∀ v, F'.degree v ≤ D := by
    intro v
    rw [← e.degree_eq v]
    exact hmax (e v)
  have hcount : F'.edgeSet.ncard = F.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using e.card_edgeFinset_eq
  have hright' : ∀ v ∈ rightF', F'.degree v ≤ d := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    rw [← e.degree_eq, e.apply_symm_apply]
    exact hrightF u hu
  have hbalance' : F'.edgeSet.ncard = d * rightF'.card := by rw [hcount, hrightCard, hbalance]
  have hhalf' : Fintype.card V ≤ 2 * rightF'.card := by rw [hrightCard]; exact hhalf
  have hloss' : ∀ f : F'.Copy H, Disjoint (copyRawEdges f) prior →
      ((copyRawEdges f ∩ removed).card : ℝ) ≤ nearRegularLossFraction B d * F'.edgeSet.ncard := by
    intro f hf
    have h := hloss (f.comp e.symm.toCopy) (by simpa only [copyRawEdges_comp_iso] using hf)
    simpa only [copyRawEdges_comp_iso, hcount] using h
  have horient' : ∀ f : F'.Copy H, Disjoint (copyRawEdges f) prior →
      (d : ℝ) * (incidenceOrientationDefects F' f rightF' (highHostVertices K P) d).card ≤
        (F'.edgeSet.ncard : ℝ) / 32 := by
    intro f hf
    have h := horient (f.comp e.symm.toCopy) (by simpa only [copyRawEdges_comp_iso] using hf)
    have hc := incidenceOrientationDefects_card_comp_iso F F' f e.symm rightF (highHostVertices K P) d
    simpa only [hc, hcount, rightF'] using h
  have hgood' : ∀ f : F'.Copy H, Disjoint (copyRawEdges f) prior →
      copyRawEdges f ∉ starImagePatterns H J (copyVertices f) (tolerantTupleOrder d)
        F'.edgeSet.ncard D P ((F'.edgeSet.ncard : ℝ) / 128 *
          Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) := by
    intro f hf
    have h := hgood (f.comp e.symm.toCopy) (by simpa only [copyRawEdges_comp_iso] using hf)
    simpa only [copyRawEdges_comp_iso, copyVertices_comp_iso, hcount] using h
  exact hd₀ d hd U W (Fintype.card V) D P hdP F' G K H J hF' hFG' hH hJ hmin' hmax' hDpow hhost hGpos
    rightF' rightG hright' hbalance' hhalf' hcover hrightG hfirst hsecond Λ prior removed hΛ hKedges hcutoff
    hcross hinitial hprior hloss' horient' hgood'

end Erdos911
