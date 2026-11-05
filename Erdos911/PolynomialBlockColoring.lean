import Erdos911.BlockBudgetBounds
import Erdos911.DenseWitnessBound
import Erdos911.SparseBlockColoring

namespace Erdos911

/-- The block and residual coloring criterion with all marking parameters
chosen uniformly. The remaining assumptions concern the block packing,
repeated uses, the target's local density, and earlier edge deletions. -/
theorem polynomial_sparse_block_coloring (A : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
      [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
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
  obtain ⟨d₁, hd₁⟩ := baseline_coloring_parameters_uniform A
  obtain ⟨d₂, hd₂⟩ := eventually_baseline_residual_bounds A
  obtain ⟨d₃, hd₃⟩ := eventually_baseline_block_budget A B
  refine ⟨max d₁ (max d₂ d₃), ?_⟩
  intro d hd U W _ _ _ _ n F _ G H K _ _ hF hFG hHK D hmin hmax hhost hDpow hm hlocal P hP hrepeated hnodense hdeleted
  classical
  have hd₁' : d₁ ≤ d := (le_max_left _ _).trans hd
  have hd₂' : d₂ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd₃' : d₃ ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  obtain ⟨v⟩ := hF.nonempty
  have hdn : d ≤ n := by
    simpa only [Fintype.card_fin] using (hmin v).trans (F.degree_lt_card_verts v).le
  have hdD : d ≤ D := (hmin v).trans (hmax v)
  have haverage : d * n ≤ 2 * F.edgeFinset.card := by
    calc
      d * n = ∑ _ : Fin n, d := by simp [mul_comm]
      _ ≤ ∑ v, F.degree v := Finset.sum_le_sum (fun v _ => hmin v)
      _ = 2 * F.edgeFinset.card := F.sum_degrees_eq_twice_card_edges
  obtain ⟨hdpos, hD, hdBlock, horder, hqD, havgBlock, hpB₀, hpB₁, hscale,
      hq, hsmall, hgap, hα₀, hα₁, hp₀, hp₁, hseed, hretention, hlog⟩ :=
    hd₁ d hd₁' D hdD hDpow n F.edgeFinset.card hdn haverage
  have hlogd : 1 ≤ Real.log d := by linarith [(hd₂ d hd₂').2.1]
  have hloglog : 1 ≤ Real.log (Real.log d) := (hd₂ d hd₂').2.2.1
  have hFedges : 0 < F.edgeSet.ncard := by
    have h := (hdpos.trans_le (hmin v)).trans_le (F.degree_le_card_edgeFinset v)
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using h
  have he : (0 : ℝ) < G.edgeSet.ncard := by
    exact_mod_cast hFedges.trans_le (copy_edge_ncard_le hFG.some)
  have hQ : ValidBlockPacking K (baselineBlockSize d) (1 / 4) ∅ := by
    simp [ValidBlockPacking]
  refine finite_sparse_two_scale_coloring_retained F G H K hHK hF hFG
    P ∅ (baselineBlockSize d) (baselineBlockSize d) (1 / 4) (1 / 4) (B * Real.log d)
    hP hQ (by simp [blockEdgeUnion]) hq (by omega) (by norm_num) (by norm_num) (by positivity)
    d D (baselineSeedOrder A d n) (F.edgeFinset.card / 256) (F.edgeFinset.card / 1024)
    (d / 512) (F.edgeFinset.card / 2) hdpos hmin hmax hhost hD hdBlock horder hqD hqD havgBlock
    (baselineBlockRate A d) (baselineSampleRate A d) (baselineResidualRate d)
    hpB₀ hpB₁ hscale hα₀ hα₁ hp₀ hp₁ ?_ ?_ hsmall hgap ?_ hseed hretention hlog
    ((G.edgeSet.ncard : ℝ) / 4) hdeleted ?_
  · simpa only [max_self] using hlocal
  · simpa only [Finset.union_empty] using hrepeated
  · simpa only [Finset.union_empty] using hnodense
  · exact baseline_two_scale_budget A B d (G.edgeSet.ncard : ℝ) K.edgeFinset.card
      ((G.edgeSet.ncard : ℝ) / 4) hB (by exact_mod_cast hdpos) hlogd hloglog he hm le_rfl (hd₃ d hd₃')

end Erdos911
