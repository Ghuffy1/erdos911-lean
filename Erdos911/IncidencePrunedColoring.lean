import Erdos911.IncidenceUniformCopyCertificates
import Erdos911.IncidenceSeedColoring

namespace Erdos911

/-- The incidence certificates and marks produce a coloring of the
original host once the preceding pruning has the stated copy bounds. -/
theorem incidence_coloring_after_pruning (A : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W], ∀ k D P : ℕ, d ≤ P →
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] (G : SimpleGraph U) [DecidableRel G.Adj]
      (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj],
    F.Connected → F.IsContained G → H ≤ lowEndpointPrunedGraph K P → J ≤ H →
    (∀ v, d ≤ F.degree v) → (∀ v, F.degree v ≤ D) → D ≤ d ^ A →
    (∀ w, H.degree w ≤ D) → 0 < G.edgeSet.ncard →
    ∀ (rightF : Finset (Fin k)) (rightG : Finset U),
    (∀ v ∈ rightF, F.degree v ≤ d) → F.edgeSet.ncard = d * rightF.card → k ≤ 2 * rightF.card →
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
  classical
  obtain ⟨dC, hdC⟩ := incidence_copy_certificate_uniform A B hB
  obtain ⟨dM, hdM⟩ := incidence_seed_marks A
  obtain ⟨dS, hdS⟩ := incidence_sampling_parameters_uniform A
  refine ⟨max dC (max dM dS), ?_⟩
  intro d hd U W _ _ _ _ k D P hdP F _ G _ K H J _ _ _ hF hFG hH hJ hmin hmax hDpow hhost hGpos
    rightF rightG hrightF hbalance hhalf hcover hrightG hfirst hsecond Λ prior removed hΛ hKedges hcutoff
    hcross hinitial hprior hloss horient hgood
  have hHK : H ≤ K := hH.trans (lowEndpointPrunedGraph_le K P)
  obtain ⟨v⟩ := hF.nonempty
  have hdk : d ≤ k := by
    simpa only [Fintype.card_fin] using (hmin v).trans (F.degree_lt_card_verts v).le
  have hdD : d ≤ D := (hmin v).trans (hmax v)
  obtain ⟨hd1, hlog, _, _, _, _, _, _, _, _, _⟩ := hdS d (by omega) D k hdD hDpow hdk
  have hlocal : ∀ w, w ∉ highHostVertices K P → H.degree w ≤ P := by
    intro w hw
    apply ((SimpleGraph.Copy.ofLE H K hHK).degree_le w).trans
    exact Nat.le_of_not_gt (fun h => hw ((mem_highHostVertices K P w).mpr h))
  let L := incidenceCandidateList F H J rightF (highHostVertices K P) d (tolerantSamplingSeed A d k)
    (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d)
  let C := incidenceMatchingSeeds F H J rightF (highHostVertices K P) d (tolerantSamplingSeed A d k)
    (tolerantTupleOrder d) (baselineBlockSize d) (nearRegularMatchingSize d k)
    (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) (incidenceCommonCutoff A P d)
  let X := incidenceCandidateVertices J (highHostVertices K P) A P d
  let blocks : (Fin (incidenceTupleOrder A) → W) → Finset W :=
    boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d)
  let budget := (2 * incidenceTupleMarkRate A P d) * 32 * X.card * (P : ℝ) ^ incidenceTupleOrder A
  obtain ⟨marks, hmarks, hcost⟩ := hdM d (by omega) W k D P hdk hdD hDpow hdP F H J rightF
    (highHostVertices K P) hJ hmax hhost hlocal hsecond
  have hcertificate : ∀ f : F.Copy H, Disjoint (copyRawEdges f) prior → ∃ c ∈ C,
      ∃ E : Finset (Fin k), (E.card : ℝ) ≤ nearRegularExceptionBound d k ∧
        (∀ v, (L c v).Nonempty → v ∉ E → f v ∈ L c v) ∧
        ∀ v, (L c v).Nonempty → v ∉ E → ∃ u, F.Adj v u ∧ f u ∈ highHostVertices K P := by
    intro f hf
    exact hdC d (by omega) W k D P hdP F H J K hF hJ hH hmin hmax hDpow hhost rightF
      hrightF hbalance hhalf hfirst f removed hcross (hloss f hf) (horient f hf) (hgood f hf)
  have hvertices : (X.card : ℝ) * incidenceCommonCutoff A P d ≤ 2 * H.edgeSet.ncard := by
    apply degree_threshold_vertex_budget H X _
    intro x hx
    have hJx := ((mem_incidenceCandidateVertices J (highHostVertices K P) A P d x).mp hx).2
    have hle : (J.degree x : ℝ) ≤ H.degree x := by
      exact_mod_cast (SimpleGraph.Copy.ofLE J H hJ).degree_le x
    exact hJx.trans hle
  have hHedges : (H.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard :=
    (show (H.edgeSet.ncard : ℝ) ≤ K.edgeSet.ncard by
      exact_mod_cast copy_edge_ncard_le (SimpleGraph.Copy.ofLE H K hHK)).trans hKedges
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hcapacity : budget * d ≤ (G.edgeSet.ncard : ℝ) / 128 :=
    incidence_tuple_capacity_budget A d P Λ X.card H.edgeSet.ncard G.edgeSet.ncard
      (by linarith) hPpos (by linarith) (Nat.cast_nonneg _) hvertices hHedges (by linarith)
  have hweighted : (∑ e, if marks e = true then (blocks e.2).card * (d : ℝ) else 0) ≤
      (G.edgeSet.ncard : ℝ) / 128 := by
    calc
      _ = (∑ e, if marks e = true then ((blocks e.2).card : ℝ) else 0) * d := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp only [zero_mul]
      _ ≤ budget * d := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg _)
      _ ≤ _ := hcapacity
  have hKedges' : (K.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hKedges
  apply incidence_seed_marking_coloring F G K H J hHK hFG rightG d P Λ hcover hrightG hKedges'
    (by push_cast; linarith) C L (tolerantTupleOrder d) 32 (incidenceCommonCutoff A P d)
    (nearRegularExceptionBound d k) ((G.edgeSet.ncard : ℝ) / 4) ((G.edgeSet.ncard : ℝ) / 2)
    ((G.edgeSet.ncard : ℝ) / 128) prior blocks ⟨marks, hmarks, hweighted⟩ hcertificate hinitial hprior
  have hpositive : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast hGpos
  linarith only [hpositive]

end Erdos911
