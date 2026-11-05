import Erdos911.NearRegularCopyCertificates
import Erdos911.AmbientSeedColoring
import Erdos911.DenseWitnessBound

namespace Erdos911

/-- The near-regular marking and copy certificates give an avoiding
coloring once the earlier pruning guarantees the two surviving-copy
conditions and stays within its blue-edge allowance. -/
theorem near_regular_coloring_after_pruning_ambient (A B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W], ∀ k D Δ : ℕ,
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] (G : SimpleGraph U) [DecidableRel G.Adj]
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
  classical
  obtain ⟨dC, hdC⟩ := near_regular_copy_certificate_uniform A B hB
  obtain ⟨dM, hdM⟩ := near_regular_seed_marks
  obtain ⟨dS, hdS⟩ := tolerant_sampling_parameters_uniform 3
  refine ⟨max dC (max dM dS), ?_⟩
  intro d hd U W _ _ _ _ k D Δ F _ G _ K H J _ _ _ hF hFG hHK hJ hmin hmax hGmax hdegree hDpow hhost hGpos
    hfirst hsecond Λ P hΛ hKedges hcutoff hinitial hprior hgood hloss
  have hHedges : (H.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard :=
    (show (H.edgeSet.ncard : ℝ) ≤ K.edgeSet.ncard by
      exact_mod_cast copy_edge_ncard_le (SimpleGraph.Copy.ofLE H K hHK)).trans hKedges
  obtain ⟨v⟩ := hF.nonempty
  have hdk : d ≤ k := by simpa only [Fintype.card_fin] using (hmin v).trans (F.degree_lt_card_verts v).le
  have hΔD : Δ ≤ D := by
    have hΔnonneg : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    have h := mul_le_mul_of_nonneg_right hΛ hΔnonneg
    have hreal : (Δ : ℝ) ≤ D := by nlinarith only [h, hcutoff, hΔnonneg]
    exact_mod_cast hreal
  have hdD : d ≤ D := (hmin v).trans ((hmax v).trans hΔD)
  obtain ⟨hd1, hlog, _, hε, _, _, _, _, _, _, _⟩ := hdS d (by omega) D k hdD hDpow hdk
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hmaxD : ∀ v, F.degree v ≤ D := fun v => (hmax v).trans hΔD
  let C := largeMatchingSeeds F H J (tolerantSamplingSeed 3 d k) (tolerantTupleOrder d)
    (baselineBlockSize d) (nearRegularMatchingSize d k) (1 - 4 * tolerantSamplingError d)
      (nearRegularCommonCutoff D d)
  let X := nearRegularCandidateVertices J D d
  let blocks : (Fin 128 → W) → Finset W := boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d)
  let budget := (2 * nearRegularTupleMarkRate D d) * 32 * X.card * (D : ℝ) ^ 128
  obtain ⟨marks, hmarks, hcost⟩ := hdM d (by omega) W k D hdk hdD hDpow F H J hJ hmaxD hhost hsecond
  have hcertificate : ∀ f : F.Copy H, Disjoint (copyRawEdges f) P → ∃ c ∈ C, ∃ E : Finset (Fin k),
      (E.card : ℝ) ≤ nearRegularExceptionBound d k ∧
      ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J (tolerantSamplingSeed 3 d k)
        (1 - 4 * tolerantSamplingError d) c v := by
    intro f hf
    exact hdC d (by omega) W k D Δ F H J hF hJ hmin hmax hΔD hdegree hDpow hhost hfirst f
      (hgood f hf) (hloss f hf)
  have hvertices : (X.card : ℝ) * nearRegularCommonCutoff D d ≤ 2 * H.edgeSet.ncard := by
    apply degree_threshold_vertex_budget H X _
    intro x hx
    have hJx := (mem_nearRegularCandidateVertices J D d x).mp hx
    have hle : (J.degree x : ℝ) ≤ H.degree x := by
      exact_mod_cast (SimpleGraph.Copy.ofLE J H hJ).degree_le x
    exact hJx.trans hle
  have hcapacity : budget * Δ ≤ (G.edgeSet.ncard : ℝ) / 128 :=
    near_regular_tuple_capacity_budget d D Λ Δ X.card H.edgeSet.ncard G.edgeSet.ncard
      (by linarith) hDpos (by linarith) (Nat.cast_nonneg _) hvertices hHedges hcutoff
  have htotal : (G.edgeSet.ncard : ℝ) / 4 + (G.edgeSet.ncard : ℝ) / 2 + budget * Δ < G.edgeSet.ncard := by
    have hpos : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast hGpos
    linarith only [hcapacity, hpos]
  exact seed_matching_coloring_after_deletions_ambient F G K H J hHK hFG Δ hGmax (tolerantSamplingSeed 3 d k)
    (tolerantTupleOrder d) 32 (1 - 4 * tolerantSamplingError d) (nearRegularCommonCutoff D d)
    (nearRegularExceptionBound d k) ((G.edgeSet.ncard : ℝ) / 4) ((G.edgeSet.ncard : ℝ) / 2) budget (by linarith) P C blocks
    ⟨marks, hmarks, hcost⟩ hcertificate hinitial hprior htotal

theorem near_regular_coloring_after_pruning (A B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W], ∀ k D Δ : ℕ,
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj] (G : SimpleGraph U) [DecidableRel G.Adj]
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
  obtain ⟨d₀, hd₀⟩ := near_regular_coloring_after_pruning_ambient A B hB
  refine ⟨d₀, ?_⟩
  intro d hd U W _ _ _ _ k D Δ F _ G _ H J _ _ hF hFG hJ hmin hmax hGmax hdegree hDpow hhost hGpos
    hfirst hsecond Λ P hΛ hHedges hcutoff hprior hgood hloss
  have hinitial : ∀ f : G.Copy H,
      ((copyRawEdges f ∩ (H \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4 := by
    intro f
    have hself : (H \ H).edgeFinset = ∅ := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff, Set.mem_sdiff, Finset.notMem_empty]
      tauto
    rw [hself, Finset.inter_empty, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  exact hd₀ d hd U W k D Δ F G H H J hF hFG le_rfl hJ hmin hmax hGmax hdegree hDpow hhost hGpos
    hfirst hsecond Λ P hΛ hHedges hcutoff hinitial hprior hgood hloss

end Erdos911
