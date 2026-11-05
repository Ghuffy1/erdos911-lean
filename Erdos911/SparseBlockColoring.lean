import Erdos911.SampledOrdinaryAssignments
import Erdos911.TwoScaleBlockColoring
import Erdos911.DeletedEdgeCapacity

namespace Erdos911

/-- A finite two-color obstruction combining degree/bad-support deletions,
two-scale block marks, and the sampled residual-edge marks. The quantitative
parameter conditions are explicit and uniform in the host order. -/
theorem finite_sparse_two_scale_coloring_retained {n : ℕ} {U W : Type*}
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (G : SimpleGraph U) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (hF : F.Connected) (hFG : F.IsContained G)
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (ρ₁ ρ₂ σ : ℝ)
    (hP : ValidBlockPacking K q₁ ρ₁ P) (hQ : ValidBlockPacking K q₂ ρ₂ Q)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q))
    (hq₁ : 2 ≤ q₁) (hq₂ : 0 < q₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hσ : 0 ≤ σ)
    (d D s bBlock j dBlock bResidual : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hD : 2 ≤ D)
    (hdBlock : 4 ≤ dBlock) (hdBlockOrder : dBlock ≤ n)
    (hq₁D : q₁ ≤ D) (hq₂D : q₂ ≤ D) (haverage : dBlock * n ≤ 2 * bBlock)
    (pBlock α pResidual : ℝ)
    (hpBlock₀ : 0 ≤ pBlock) (hpBlock₁ : pBlock ≤ 1)
    (hblockScale : 32 * Real.log D ≤ pBlock * dBlock)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hpResidual₀ : 0 < pResidual) (hpResidual₁ : pResidual ≤ 1)
    (hlocal : ∀ S : Finset U, S.card ≤ 2 * max q₁ q₂ →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ σ * S.card)
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
    (hbudget : L + (2 * pBlock) * (2 * σ * K.edgeFinset.card / (ρ₁ * q₁) +
        2 * σ * K.edgeFinset.card / (ρ₂ * q₂)) + 2 * pResidual * K.edgeFinset.card < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  obtain ⟨blockMarks, hblockCost, hblockPoor⟩ := two_scale_block_rich_branch_ambient F G H K hF
    P Q q₁ q₂ ρ₁ ρ₂ σ hP hQ hcross (by omega) hq₂ hρ₁ hρ₂ hσ
    bBlock j dBlock D hdBlock (by simpa using hdBlockOrder) hD hq₁D hq₂D
    (by simpa using haverage) hhost pBlock hpBlock₀ hpBlock₁ hblockScale hlocal hrepeated
  let H₁ := H.deleteEdges (blockMarks : Set (Sym2 W))
  let J := blockResidual H₁ (P ∪ Q)
  have hH₁H : H₁ ≤ H := H.deleteEdges_le _
  have hJH₁ : J ≤ H₁ := blockResidual_le H₁ (P ∪ Q)
  have hJK : J ≤ K := hJH₁.trans (hH₁H.trans hHK)
  have hJambient : J ≤ H.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W)) :=
    SimpleGraph.deleteEdges_mono hH₁H
  have hhost₁ : ∀ w, H₁.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE H₁ H hH₁H).degree_le w).trans (hhost w)
  have hnodenseJ : ∀ A B : Finset W, A.card = q₁ → B.card = q₁ → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ₁ * q₁ * q₁ := by
    intro A B hA hB hAB
    have hm : (crossEdges J A B : ℝ) ≤
        crossEdges (H.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W))) A B := by
      exact_mod_cast crossEdges_mono hJambient A B
    exact hm.trans (hnodense A B hA hB hAB)
  have hlarge : ∀ f : F.Copy H₁,
      bResidual + 17 * (F \ copyRetainedGraph J f).edgeFinset.card ≤ F.edgeFinset.card := by
    intro f
    have hpoor : (copyRawEdges f ∩ blockEdgeUnion (P ∪ Q)).card < bBlock + 3 * j := by
      simpa only [copyRawEdges_ofLE_comp] using hblockPoor f
    have hmissing := copy_missing_edges_le J f (blockEdgeUnion (P ∪ Q)) (by
      intro u v huv hn
      exact (SimpleGraph.deleteEdges_adj).mpr ⟨huv, hn⟩)
    omega
  obtain ⟨residualMarks, _, hresidualCost, hfree⟩ := finite_sparse_residual_obstruction F H₁ J hF hJH₁
    d D s q₁ bResidual hd hmin hmax hhost₁ (by omega) hq₁ hsmall
    ρ₁ α pResidual hρ₁.le hα₀ hα₁ hpResidual₀ hpResidual₁ hgap hnodenseJ hseed hlarge hlog
  have hresidualCostK : (residualMarks.card : ℝ) ≤ 2 * pResidual * K.edgeFinset.card := by
    have hcard : (J.edgeFinset.card : ℝ) ≤ K.edgeFinset.card := by
      exact_mod_cast Finset.card_le_card (SimpleGraph.edgeFinset_mono hJK)
    exact hresidualCost.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
  let marked := (K \ H).edgeFinset ∪ (blockMarks ∪ residualMarks)
  have hbase : K.deleteEdges ((K \ H).edgeFinset : Set (Sym2 W)) = H := by
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_sdiff]
    exact K.deleteEdges_sdiff_eq_of_le hHK
  have hred : ¬F.IsContained (K.deleteEdges (marked : Set (Sym2 W))) := by
    have heq : K.deleteEdges (marked : Set (Sym2 W)) = H₁.deleteEdges (residualMarks : Set (Sym2 W)) := by
      change K.deleteEdges (↑((K \ H).edgeFinset ∪ (blockMarks ∪ residualMarks))) = _
      rw [Finset.coe_union, Finset.coe_union, ← K.deleteEdges_deleteEdges, hbase,
        ← H.deleteEdges_deleteEdges]
    rw [heq]
    exact hfree
  apply avoiding_coloring_of_deleted_capacity F G K hFG marked hred
  intro g
  have hnat := (copy_capacity_union_inter (copyRawEdges g) (K \ H).edgeFinset
    (blockMarks ∪ residualMarks)).trans
      (Nat.add_le_add_left (copy_capacity_union (copyRawEdges g) blockMarks residualMarks) _)
  have hreal : ((copyRawEdges g ∩ marked).card : ℝ) ≤
      (copyRawEdges g ∩ (K \ H).edgeFinset).card + (copyRawEdges g ∩ blockMarks).card +
        residualMarks.card := by
    exact_mod_cast (by simpa only [marked, Nat.add_assoc] using hnat)
  have hstrict : ((copyRawEdges g ∩ marked).card : ℝ) < G.edgeSet.ncard := by
    linarith [hdeleted g, hblockCost g]
  exact_mod_cast hstrict

theorem finite_sparse_two_scale_coloring {n : ℕ} {U W : Type*}
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (G : SimpleGraph U) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (hF : F.Connected) (hFG : F.IsContained G)
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (ρ₁ ρ₂ σ : ℝ)
    (hP : ValidBlockPacking K q₁ ρ₁ P) (hQ : ValidBlockPacking K q₂ ρ₂ Q)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q))
    (hq₁ : 2 ≤ q₁) (hq₂ : 0 < q₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hσ : 0 ≤ σ)
    (d D s bBlock j dBlock bResidual : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hD : 2 ≤ D)
    (hdBlock : 4 ≤ dBlock) (hdBlockOrder : dBlock ≤ n)
    (hq₁D : q₁ ≤ D) (hq₂D : q₂ ≤ D) (haverage : dBlock * n ≤ 2 * bBlock)
    (pBlock α pResidual : ℝ)
    (hpBlock₀ : 0 ≤ pBlock) (hpBlock₁ : pBlock ≤ 1)
    (hblockScale : 32 * Real.log D ≤ pBlock * dBlock)
    (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hpResidual₀ : 0 < pResidual) (hpResidual₁ : pResidual ≤ 1)
    (hlocal : ∀ S : Finset U, S.card ≤ 2 * max q₁ q₂ →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hrepeated : ∀ f : F.Copy H, repeatedEdgeVolume (P ∪ Q) (copyRawEdges f) < 3 * j)
    (hsmall : 2 * q₁ ≤ d) (hgap : ρ₁ * d + q₁ < (11 / 16 : ℝ) * d)
    (hnodense : ∀ A B : Finset W, A.card = q₁ → B.card = q₁ → Disjoint A B →
      (crossEdges (K.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W))) A B : ℝ) ≤ ρ₁ * q₁ * q₁)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-((1 / 16 : ℝ) ^ 2 * (α * d)) / 128)) ≤ s)
    (hretention : bResidual + 17 * (bBlock + 3 * j) ≤ F.edgeFinset.card)
    (hlog : Real.log (8 * seedAssignmentCountBound n D D s q₁ / pResidual) ≤ pResidual * bResidual / 2)
    (L : ℝ)
    (hdeleted : ∀ g : G.Copy K, ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤ L)
    (hbudget : L + (2 * pBlock) * (2 * σ * K.edgeFinset.card / (ρ₁ * q₁) +
        2 * σ * K.edgeFinset.card / (ρ₂ * q₂)) + 2 * pResidual * K.edgeFinset.card < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  apply finite_sparse_two_scale_coloring_retained F G H K hHK hF hFG P Q q₁ q₂ ρ₁ ρ₂ σ
    hP hQ hcross hq₁ hq₂ hρ₁ hρ₂ hσ d D s bBlock j dBlock bResidual hd hmin hmax hhost hD
    hdBlock hdBlockOrder hq₁D hq₂D haverage pBlock α pResidual hpBlock₀ hpBlock₁ hblockScale
    hα₀ hα₁ hpResidual₀ hpResidual₁ hlocal hrepeated hsmall hgap ?_ hseed hretention hlog L hdeleted hbudget
  intro A B hA hB hAB
  have hmono : (crossEdges (H.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W))) A B : ℝ) ≤
      crossEdges (K.deleteEdges (blockEdgeUnion (P ∪ Q) : Set (Sym2 W))) A B := by
    exact_mod_cast crossEdges_mono (SimpleGraph.deleteEdges_mono hHK) A B
  exact hmono.trans (hnodense A B hA hB hAB)

end Erdos911
