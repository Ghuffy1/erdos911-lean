import Erdos911.NearRegularPrunedColoring
import Erdos911.RelabelBlockColoring

namespace Erdos911

theorem copyVertices_comp_iso {U V W : Type*} [Fintype U] [Fintype V] [DecidableEq W]
    {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G.Copy H) (e : F ≃g G) : copyVertices (f.comp e.toCopy) = copyVertices f := by
  classical
  ext w
  simp only [copyVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨e u, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨e.symm v, by simp⟩

theorem copy_missing_edge_count_comp_iso {U V W : Type*}
    [Fintype U] [Fintype V] [Fintype W]
    {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}
    (J : SimpleGraph W) (f : G.Copy H) (e : F ≃g G) :
    (F \ copyRetainedGraph J (f.comp e.toCopy)).edgeSet.ncard =
      (G \ copyRetainedGraph J f).edgeSet.ncard := by
  classical
  let e' : (F \ copyRetainedGraph J (f.comp e.toCopy)) ≃g (G \ copyRetainedGraph J f) := {
    toEquiv := e.toEquiv
    map_rel_iff' := by
      intro u v
      change (G.Adj (e u) (e v) ∧ ¬(G.Adj (e u) (e v) ∧ J.Adj (f (e u)) (f (e v)))) ↔
        (F.Adj u v ∧ ¬(F.Adj u v ∧ J.Adj (f (e u)) (f (e v))))
      rw [e.map_rel_iff]
  }
  simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using e'.card_edgeFinset_eq

/-- The near-regular coloring criterion applies to component models on
arbitrary finite vertex types, with one degree threshold for all types. -/
theorem near_regular_coloring_after_pruning_ambient_general (A B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V U W : Type*)
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D Δ : ℕ) (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U) [DecidableRel G.Adj]
      (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj],
    F.Connected → F.IsContained G → H ≤ K → J ≤ H → (∀ v, d ≤ F.degree v) →
    (∀ v, F.degree v ≤ Δ) → (∀ v, G.degree v ≤ Δ) →
    (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower → D ≤ d ^ 3 →
    (∀ w, H.degree w ≤ D) → 0 < G.edgeSet.ncard →
    (∀ X Y : Finset W, X.card = baselineBlockSize d → Y.card = baselineBlockSize d →
      Disjoint X Y → (crossEdges J X Y : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) →
    (∀ X Y : Finset W, X.card = nearRegularBlockSize d → Y.card = nearRegularBlockSize d →
      Disjoint X Y → (crossEdges J X Y : ℝ) ≤
        nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) →
    ∀ (Λ : ℝ) (P : Finset (Sym2 W)), 1 ≤ Λ → (K.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard →
    16 * Λ * Δ ≤ D →
    (∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4) →
    (∀ f : G.Copy K, ((copyRawEdges f ∩ P).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 2) →
    (∀ f : F.Copy H, Disjoint (copyRawEdges f) P →
      ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) (tolerantTupleOrder d) D
        ((F.edgeSet.ncard : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d))) →
    (∀ f : F.Copy H, Disjoint (copyRawEdges f) P →
      ((F \ copyRetainedGraph J f).edgeSet.ncard : ℝ) ≤ nearRegularLossFraction B d * F.edgeSet.ncard) →
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  obtain ⟨d₀, hd₀⟩ := near_regular_coloring_after_pruning_ambient A B hB
  refine ⟨d₀, ?_⟩
  intro d hd V U W _ _ _ _ _ _ D Δ F _ G _ K H J _ _ _ hF hFG hHK hJ hmin hmax hGmax hdegree hDpow
    hhost hGpos hfirst hsecond Λ P hΛ hbudget hcutoff hinitial hprior hgood hloss
  classical
  let vertexEquiv := (Fintype.equivFin V).symm
  let F' := F.comap vertexEquiv
  let e : F' ≃g F := SimpleGraph.Iso.comap vertexEquiv F
  have hF' : F'.Connected := e.connected_iff.mpr hF
  have hFG' : F'.IsContained G := (show F'.IsContained F from ⟨e.toCopy⟩).trans hFG
  have hmin' : ∀ v, d ≤ F'.degree v := by
    intro v
    rw [← e.degree_eq v]
    exact hmin (e v)
  have hmax' : ∀ v, F'.degree v ≤ Δ := by
    intro v
    rw [← e.degree_eq v]
    exact hmax (e v)
  have hcount : F'.edgeSet.ncard = F.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using e.card_edgeFinset_eq
  have hgood' : ∀ f : F'.Copy H, Disjoint (copyRawEdges f) P →
      ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) (tolerantTupleOrder d) D
        ((F'.edgeSet.ncard : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d)) := by
    intro f hf
    have h := hgood (f.comp e.symm.toCopy) (by simpa only [copyRawEdges_comp_iso] using hf)
    simpa only [copyVertices_comp_iso, copyRawEdges_comp_iso, hcount] using h
  have hloss' : ∀ f : F'.Copy H, Disjoint (copyRawEdges f) P →
      ((F' \ copyRetainedGraph J f).edgeSet.ncard : ℝ) ≤ nearRegularLossFraction B d * F'.edgeSet.ncard := by
    intro f hf
    have h := hloss (f.comp e.symm.toCopy) (by simpa only [copyRawEdges_comp_iso] using hf)
    simpa only [copy_missing_edge_count_comp_iso, hcount] using h
  exact hd₀ d hd U W (Fintype.card V) D Δ F' G K H J hF' hFG' hHK hJ hmin' hmax' hGmax hdegree
    hDpow hhost hGpos hfirst hsecond Λ P hΛ hbudget hcutoff hinitial hprior hgood' hloss'

theorem near_regular_coloring_after_pruning_general (A B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V U W : Type*)
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D Δ : ℕ) (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U) [DecidableRel G.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj],
    F.Connected → F.IsContained G → J ≤ H → (∀ v, d ≤ F.degree v) →
    (∀ v, F.degree v ≤ Δ) → (∀ v, G.degree v ≤ Δ) →
    (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower → D ≤ d ^ 3 →
    (∀ w, H.degree w ≤ D) → 0 < G.edgeSet.ncard →
    (∀ X Y : Finset W, X.card = baselineBlockSize d → Y.card = baselineBlockSize d →
      Disjoint X Y → (crossEdges J X Y : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) →
    (∀ X Y : Finset W, X.card = nearRegularBlockSize d → Y.card = nearRegularBlockSize d →
      Disjoint X Y → (crossEdges J X Y : ℝ) ≤
        nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) →
    ∀ (Λ : ℝ) (P : Finset (Sym2 W)), 1 ≤ Λ → (H.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard →
    16 * Λ * Δ ≤ D →
    (∀ f : G.Copy H, ((copyRawEdges f ∩ P).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 2) →
    (∀ f : F.Copy H, Disjoint (copyRawEdges f) P →
      ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) (tolerantTupleOrder d) D
        ((F.edgeSet.ncard : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d))) →
    (∀ f : F.Copy H, Disjoint (copyRawEdges f) P →
      ((F \ copyRetainedGraph J f).edgeSet.ncard : ℝ) ≤ nearRegularLossFraction B d * F.edgeSet.ncard) →
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  obtain ⟨d₀, hd₀⟩ := near_regular_coloring_after_pruning_ambient_general A B hB
  refine ⟨d₀, ?_⟩
  intro d hd V U W _ _ _ _ _ _ D Δ F _ G _ H J _ _ hF hFG hJ hmin hmax hGmax hdegree hDpow
    hhost hGpos hfirst hsecond Λ P hΛ hbudget hcutoff hprior hgood hloss
  have hinitial : ∀ f : G.Copy H,
      ((copyRawEdges f ∩ (H \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4 := by
    intro f
    have hself : (H \ H).edgeFinset = ∅ := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff, Set.mem_sdiff, Finset.notMem_empty]
      tauto
    rw [hself, Finset.inter_empty, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  exact hd₀ d hd V U W D Δ F G H H J hF hFG le_rfl hJ hmin hmax hGmax hdegree hDpow
    hhost hGpos hfirst hsecond Λ P hΛ hbudget hcutoff hinitial hprior hgood hloss

end Erdos911
