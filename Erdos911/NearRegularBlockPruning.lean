import Erdos911.NearRegularBlockBudget
import Erdos911.NearRegularCopyCertificates
import Erdos911.TwoScaleBlockColoring

namespace Erdos911

/-- The concrete two-scale marking leaves every surviving connected test
copy with the prescribed small block-edge loss. Its blue capacity is
measured on copies in the original ambient graph. -/
theorem near_regular_block_pruning (M C : ℝ) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V U W : Type*)
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W], ∀ D : ℕ,
      ∀ (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U)
        (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
        (P Q : Finset (RectangleBlock W)) (E : ℝ),
      F.Connected → (∀ v, d ≤ F.degree v) → d ≤ D → D ≤ d ^ 3 →
      (∀ w, H.degree w ≤ D) →
      ValidBlockPacking K (baselineBlockSize d) (1 / 4 : ℝ) P →
      ValidBlockPacking K (nearRegularBlockSize d) (nearRegularRectangleDensity d) Q →
      Disjoint (blockEdgeUnion P) (blockEdgeUnion Q) →
      0 ≤ E → (K.edgeFinset.card : ℝ) ≤ M * d * E →
      (∀ S : Finset U, S.card ≤ 2 * max (baselineBlockSize d) (nearRegularBlockSize d) →
        ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      (∀ f : F.Copy H, repeatedEdgeVolume (P ∪ Q) (copyRawEdges f) <
        3 * nearRegularRepeatThreshold d F.edgeSet.ncard) →
      ∃ marked : Finset (Sym2 W),
        (∀ g : G.Copy K, ((copyRawEdges g ∩ marked).card : ℝ) ≤ (1 / 16 : ℝ) * E) ∧
        ∀ f : F.Copy (H.deleteEdges (marked : Set (Sym2 W))),
          ((copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) ∩
            blockEdgeUnion (P ∪ Q)).card : ℝ) ≤ nearRegularLossFraction 1024 d * F.edgeSet.ncard := by
  classical
  obtain ⟨dP, hdP⟩ := near_regular_pruning_parameters_uniform
  obtain ⟨dB, hdB⟩ := near_regular_block_parameters_uniform M C hC
  obtain ⟨dQ, hdQ⟩ := eventually_baseline_residual_bounds 3
  refine ⟨max dP (max dB dQ), ?_⟩
  intro d hd V U W _ _ _ _ _ _ D F _ G H K _ _ P Q E hF hmin hdD hDpow hhost hP hQ hcross hE hbudget hlocal hrepeat
  obtain ⟨hd4, hlog, _, _, _, _, hq₁, hqsmall⟩ := hdQ d (by omega)
  obtain ⟨v⟩ := hF.nonempty
  have hdk : d ≤ Fintype.card V := (hmin v).trans (F.degree_lt_card_verts v).le
  have haverage : (d : ℝ) * Fintype.card V ≤ 2 * F.edgeSet.ncard := by
    have h := (degree_edge_count_bounds F d F.maxDegree hmin F.degree_le_maxDegree).1
    linarith only [h]
  obtain ⟨hdegree, hdegreeD, hblockAverage, _, _, hloss⟩ := hdP d (by omega)
    (Fintype.card V) F.edgeSet.ncard hdk haverage
  obtain ⟨hp₀, hp₁, hscale, hcost⟩ := hdB d (by omega) D hdD hDpow
  have hq₁d : baselineBlockSize d ≤ d := by
    have h : (baselineBlockSize d : ℝ) ≤ d := by linarith [Nat.cast_nonneg (α := ℝ) d]
    exact_mod_cast h
  have hq₂ := nearRegularBlockSize_bounds d (by omega)
  have hρ : 0 < nearRegularRectangleDensity d := by
    unfold nearRegularRectangleDensity
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < d by omega)) _
  obtain ⟨marked, hcapacity, hpoor⟩ := two_scale_block_rich_branch_ambient F G H K hF P Q
    (baselineBlockSize d) (nearRegularBlockSize d) (1 / 4) (nearRegularRectangleDensity d)
    (C * Real.log d) hP hQ hcross (by omega) (by omega) (by norm_num) hρ
    (mul_nonneg hC (by linarith)) (nearRegularBlockThreshold d F.edgeSet.ncard)
    (nearRegularRepeatThreshold d F.edgeSet.ncard) (nearRegularEffectiveDegree d) D hdegree
    (hdegreeD.trans hdk) (by omega) (hq₁d.trans hdD) (hq₂.2.1.trans hdD) hblockAverage
    hhost (nearRegularBlockRate d) hp₀ hp₁ hscale hlocal hrepeat
  refine ⟨marked, ?_, ?_⟩
  · intro g
    exact (hcapacity g).trans (hcost K.edgeFinset.card E (Nat.cast_nonneg _) hE hbudget)
  · intro f
    have h : ((copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) ∩
        blockEdgeUnion (P ∪ Q)).card : ℝ) ≤
          (nearRegularBlockThreshold d F.edgeSet.ncard +
            3 * nearRegularRepeatThreshold d F.edgeSet.ncard : ℕ) := by
      exact_mod_cast (hpoor f).le
    exact h.trans hloss

end Erdos911
