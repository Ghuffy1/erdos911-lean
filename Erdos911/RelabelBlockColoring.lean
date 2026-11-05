import Erdos911.PolynomialBlockColoring

namespace Erdos911

theorem copyRawEdges_comp_iso {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
    {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G.Copy H) (e : F ≃g G) : copyRawEdges (f.comp e.toCopy) = copyRawEdges f := by
  classical
  ext x
  rw [mem_copyRawEdges_iff_exists, mem_copyRawEdges_iff_exists]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨e.mapEdgeSet a, ?_⟩
    change Sym2.map (f : V → W) (Sym2.map (e : U → V) a.val) = x
    rw [Sym2.map_map]
    exact ha
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := e.mapEdgeSet.surjective a
    refine ⟨b, ?_⟩
    change Sym2.map ((f : V → W) ∘ (e : U → V)) b.val = x
    rw [← Sym2.map_map]
    exact ha

/-- The polynomial block criterion is invariant under relabelling the
test graph, including the component models used in type selection. -/
theorem polynomial_sparse_block_coloring_general (A : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V U W : Type*)
      [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
      ∀ (F : SimpleGraph V) [DecidableRel F.Adj]
      (G : SimpleGraph U) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj],
      F.Connected → F.IsContained G → H ≤ K → ∀ D : ℕ,
      (∀ v, d ≤ F.degree v) → (∀ v, F.degree v ≤ D) →
      (∀ w, H.degree w ≤ D) → D ≤ d ^ A →
      (K.edgeFinset.card : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard →
      (∀ S : Finset U, S.card ≤ 2 * baselineBlockSize d →
        ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ B * Real.log d * S.card) →
      ∀ P : Finset (RectangleBlock W), ValidBlockPacking K (baselineBlockSize d) (1 / 4) P →
      (∀ f : F.Copy H, repeatedEdgeVolume P (copyRawEdges f) < 3 * (F.edgeFinset.card / 1024)) →
      (∀ S T : Finset W, S.card = baselineBlockSize d → T.card = baselineBlockSize d →
        Disjoint S T → (crossEdges (H.deleteEdges (blockEdgeUnion P : Set (Sym2 W))) S T : ℝ) ≤
          (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) →
      (∀ g : G.Copy K, ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤
        (G.edgeSet.ncard : ℝ) / 4) →
      ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  obtain ⟨d₀, hd₀⟩ := polynomial_sparse_block_coloring A B hB
  refine ⟨d₀, ?_⟩
  intro d hd V U W _ _ _ _ _ _ F _ G H K _ _ hF hFG hHK D hmin hmax hhost hDpow hm hlocal P hP hrepeated hnodense hdeleted
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
  have hmax' : ∀ v, F'.degree v ≤ D := by
    intro v
    rw [← e.degree_eq v]
    exact hmax (e v)
  have hcount : F'.edgeFinset.card = F.edgeFinset.card := e.card_edgeFinset_eq
  have hrepeat' : ∀ f : F'.Copy H,
      repeatedEdgeVolume P (copyRawEdges f) < 3 * (F'.edgeFinset.card / 1024) := by
    intro f
    have h := hrepeated (f.comp e.symm.toCopy)
    rw [copyRawEdges_comp_iso, ← hcount] at h
    exact h
  exact hd₀ d hd U W (Fintype.card V) F' G H K hF' hFG' hHK D hmin' hmax' hhost hDpow
    hm hlocal P hP hrepeat' hnodense hdeleted

end Erdos911
