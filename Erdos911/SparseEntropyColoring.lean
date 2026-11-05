import Erdos911.ConditionalSeedColoring
import Erdos911.SampledOrdinaryAssignments
import Erdos911.TwoScaleBlockColoring
import Erdos911.HostPruningComposition

namespace Erdos911

/-- Block marks and conditional residual marks give a full-target entropy
criterion. The blue count is taken in the original ambient host. -/
theorem finite_sparse_two_scale_entropy_coloring {n : ℕ} {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (K H : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (hHK : H ≤ K) (hF : F.Connected) (hFG : F.IsContained G)
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (ρ₁ ρ₂ σ : ℝ)
    (hP : ValidBlockPacking K q₁ ρ₁ P) (hQ : ValidBlockPacking K q₂ ρ₂ Q)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q))
    (hq₁ : 2 ≤ q₁) (hq₂ : 0 < q₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hσ : 0 ≤ σ)
    (d D ΔG s bBlock j dBlock bResidual : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hD : 2 ≤ D)
    (hΔG : ∀ v, G.degree v ≤ ΔG) (hK : 0 < K.edgeFinset.card)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v)
    (hdBlock : 4 ≤ dBlock) (hdBlockOrder : dBlock ≤ n)
    (hq₁D : q₁ ≤ D) (hq₂D : q₂ ≤ D) (haverage : dBlock * n ≤ 2 * bBlock)
    (pBlock α pResidual : ℝ)
    (hpBlock₀ : 0 ≤ pBlock) (hpBlock₁ : pBlock ≤ 1)
    (hblockScale : 32 * Real.log D ≤ pBlock * dBlock)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hpResidual₀ : 0 < pResidual) (hpResidual₁ : pResidual ≤ 1)
    (hlocal : ∀ S : Finset V, S.card ≤ 2 * max q₁ q₂ →
      ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hrepeated : ∀ f : F.Copy H, repeatedEdgeVolume (P ∪ Q) (copyRawEdges f) < 3 * j)
    (hsmall : 2 * q₁ ≤ d) (hgap : ρ₁ * d + q₁ < (11 / 16 : ℝ) * d)
    (hnodense : ∀ A B : Finset W, A.card = q₁ → B.card = q₁ → Disjoint A B →
      (crossEdges (H.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W))) A B : ℝ) ≤ ρ₁ * q₁ * q₁)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-((1 / 16 : ℝ) ^ 2 * (α * d)) / 128)) ≤ s)
    (hretention : bResidual + 17 * (bBlock + 3 * j) ≤ F.edgeFinset.card)
    (hlog : Real.log (8 * seedAssignmentCountBound n D D s q₁ / pResidual) ≤ pResidual * bResidual / 2)
    (L : ℝ)
    (hdeleted : ∀ g : G.Copy K, ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤ L)
    (hbase : pResidual * Real.exp (pResidual / 4) ≤ 1)
    (hbudget : componentEntropyMass G + forestCountingError (Fintype.card V)
      (Nat.card G.ConnectedComponent) K.edgeFinset.card ΔG +
      ((G.edgeSet.ncard : ℝ) - (L + 2 * pBlock *
        (2 * σ * K.edgeFinset.card / (ρ₁ * q₁) + 2 * σ * K.edgeFinset.card / (ρ₂ * q₂)))) *
        (Real.log pResidual + pResidual / 4) < 0) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  obtain ⟨blockMarks, hblockCost, hblockPoor⟩ := two_scale_block_rich_branch_ambient F G H K hF
    P Q q₁ q₂ ρ₁ ρ₂ σ hP hQ hcross (by omega) hq₂ hρ₁ hρ₂ hσ
    bBlock j dBlock D hdBlock (by simpa using hdBlockOrder) hD hq₁D hq₂D
    (by simpa using haverage) hhost pBlock hpBlock₀ hpBlock₁ hblockScale hlocal hrepeated
  let H₁ := H.deleteEdges (blockMarks : Set (Sym2 W))
  let J := blockResidual H₁ (P ∪ Q)
  have hH₁H : H₁ ≤ H := H.deleteEdges_le _
  have hH₁K : H₁ ≤ K := hH₁H.trans hHK
  have hJH₁ : J ≤ H₁ := blockResidual_le H₁ (P ∪ Q)
  have hJambient : J ≤ H.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W)) :=
    SimpleGraph.deleteEdges_mono hH₁H
  have hhost₁ : ∀ w, H₁.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE H₁ H hH₁H).degree_le w).trans (hhost w)
  have hnodenseJ : ∀ A B : Finset W, A.card = q₁ → B.card = q₁ → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ₁ * q₁ * q₁ := by
    intro A B hA hB hAB
    have hmono : (crossEdges J A B : ℝ) ≤
        crossEdges (H.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W))) A B := by
      exact_mod_cast crossEdges_mono hJambient A B
    exact hmono.trans (hnodense A B hA hB hAB)
  have hlarge : ∀ f : F.Copy H₁,
      bResidual + 17 * (F \ copyRetainedGraph J f).edgeFinset.card ≤ F.edgeFinset.card := by
    intro f
    have hpoor : (copyRawEdges f ∩ blockEdgeUnion (P ∪ Q)).card < bBlock + 3 * j := by
      simpa only [copyRawEdges_ofLE_comp] using hblockPoor f
    have hmissing := copy_missing_edges_le J f (blockEdgeUnion (P ∪ Q)) (by
      intro u v huv hn
      exact (SimpleGraph.deleteEdges_adj).mpr ⟨huv, hn⟩)
    omega
  have hcoverage := ordinary_seed_assignment_coverage F H₁ J hF hJH₁ d D s q₁ bResidual
    hd hmin hmax hhost₁ hq₁ hsmall ρ₁ α hρ₁.le hα₀ hα₁ hgap hnodenseJ hseed hlarge
  let Ltotal := L + 2 * pBlock *
    (2 * σ * K.edgeFinset.card / (ρ₁ * q₁) + 2 * σ * K.edgeFinset.card / (ρ₂ * q₂))
  have hdeleted₁ : ∀ g : G.Copy K, ((copyRawEdges g ∩ (K \ H₁).edgeFinset).card : ℝ) ≤ Ltotal := by
    intro g
    have hsum : ((copyRawEdges g ∩ (K \ H₁).edgeFinset).card : ℝ) ≤
        (copyRawEdges g ∩ (K \ H).edgeFinset).card + (copyRawEdges g ∩ blockMarks).card := by
      exact_mod_cast copy_deleted_capacity_delete_inter G K H blockMarks g
    dsimp only [Ltotal]
    linarith [hdeleted g, hblockCost g]
  exact conditional_seed_entropy_coloring G F K H₁ J hH₁K hJH₁ hFG hF ΔG D D hΔG hK
    hneighbors hedge hmax hhost₁ (by omega) (by omega) s q₁ bResidual (3 / 4) pResidual
    (by norm_num) hpResidual₀ hpResidual₁ (by simpa using hlog) hcoverage Ltotal hdeleted₁ hbase hbudget

end Erdos911
