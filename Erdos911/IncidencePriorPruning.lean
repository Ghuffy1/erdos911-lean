import Erdos911.IncidenceTypePruning
import Erdos911.IncidenceBlockPruning
import Erdos911.IncidenceClassParameters
import Erdos911.IncidenceComponentColoring
import Erdos911.NearRegularBlockExtraction
import Erdos911.CopyDeletionLifts

namespace Erdos911

/-- Extracted cross blocks, three-type pruning and block marking give
the three copy guarantees needed by the incidence coloring theorem. -/
theorem incidence_prior_pruning (A : ℕ) (M C τ : ℝ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) (hτ : 0 < τ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D P : ℕ) (G : SimpleGraph U) [DecidableRel G.Adj]
      (K H : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj],
    H ≤ lowEndpointPrunedGraph K P → (∀ v, d ≤ G.degree v) →
    d ≤ D → D ≤ d ^ A → (∀ w, H.degree w ≤ D) →
    32 * M * (d : ℝ) ^ 2 ≤ (P : ℝ) → (P : ℝ) ≤ 64 * M * (d : ℝ) ^ 2 →
    (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard →
    (∀ S : Finset U, S.card ≤ 2 * nearRegularBlockSize d →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
    ∀ left right : Finset U, G.IsBipartiteWith (left : Set U) (right : Set U) →
    (∀ v ∈ right, G.degree v = d) →
    (∀ v ∈ left, (d : ℝ) * (Real.log d) ^ τ ≤ G.degree v) →
    ∀ k e : ℕ, Real.exp ((e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
      ((componentClass G k e).card : ℝ) →
    ∃ J : SimpleGraph W, letI : DecidableRel J.Adj := Classical.decRel J.Adj
      J ≤ H ∧
      (∀ X Y : Finset W, X.card = baselineBlockSize d → Y.card = baselineBlockSize d →
        Disjoint X Y → (crossEdges J X Y : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) ∧
      (∀ X Y : Finset W, X.card = nearRegularBlockSize d → Y.card = nearRegularBlockSize d →
        Disjoint X Y → (crossEdges J X Y : ℝ) ≤
          nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) ∧
      ∃ t ∈ componentClass G k e,
        letI : DecidableRel (componentModel G t).Adj := Classical.decRel (componentModel G t).Adj
        ∃ prior removed : Finset (Sym2 W),
        (∀ x y, H.Adj x y → x ∉ highHostVertices K P → y ∈ highHostVertices K P →
          s(x, y) ∉ removed → J.Adj x y) ∧
        (∀ g : G.Copy K, ((copyRawEdges g ∩ prior).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 8) ∧
        ∀ f : (componentModel G t).Copy H, Disjoint (copyRawEdges f) prior →
          ((copyRawEdges f ∩ removed).card : ℝ) ≤
            nearRegularLossFraction 1024 d * (componentModel G t).edgeSet.ncard ∧
          (d : ℝ) * (incidenceOrientationDefects (componentModel G t) f
            (componentSide G t right) (highHostVertices K P) d).card ≤
              ((componentModel G t).edgeSet.ncard : ℝ) / 32 ∧
          copyRawEdges f ∉ starImagePatterns H J (copyVertices f) (tolerantTupleOrder d)
            (componentModel G t).edgeSet.ncard D P (((componentModel G t).edgeSet.ncard : ℝ) / 128 *
              Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) := by
  classical
  obtain ⟨dJ, hdJ⟩ := incidence_joint_pruning A M τ hM hτ
  obtain ⟨dB, hdB⟩ := incidence_block_pruning A M C hC
  obtain ⟨dQ, hdQ⟩ := near_regular_block_sizes_ordered_uniform
  obtain ⟨dL, hdL⟩ := eventually_baseline_residual_bounds A
  refine ⟨max 2 (max dJ (max dB (max dQ dL))), ?_⟩
  intro d hd U W _ _ _ _ D P G _ K H _ _ hH hmin hdD hDpow hhost hlower hupper
    hbudget hlocal left right hBip hright hleft k e hclass
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdpos : 0 < d := by omega
  have hDpos : 0 < D := by omega
  have hHK : H ≤ K := hH.trans (lowEndpointPrunedGraph_le K P)
  obtain ⟨_, hlog, _⟩ := hdL d (by omega)
  have hclasspos : (componentClass G k e).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.exp_pos _).trans_le hclass
  obtain ⟨a, hdk, ha, hak, he, haverage, hsizeUpper, horient, hside⟩ :=
    incidence_component_class_parameters G left right hBip d k e τ hdpos (by linarith)
      hτ.le hmin hright hleft hclasspos
  let cross := highLowGraph H (highHostVertices K P)
  have hcrossH : cross ≤ H := highLowGraph_le H _
  have hcrossK : cross ≤ K := hcrossH.trans hHK
  have hq := hdQ d (by omega)
  have hρ : 0 ≤ nearRegularRectangleDensity d := by unfold nearRegularRectangleDensity; positivity
  obtain ⟨P₁, P₂, hP₁, hP₂, hdisjoint, hblocks, hfirst, hsecond⟩ :=
    exists_two_scale_residual_blocks cross (baselineBlockSize d) (nearRegularBlockSize d)
      (1 / 4) (nearRegularRectangleDensity d) (by norm_num) hρ hq
  let J := blockResidual cross (P₁ ∪ P₂)
  have hJ : J ≤ H := (blockResidual_le cross _).trans hcrossH
  have hHbudget : (H.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    have hle : (H.edgeSet.ncard : ℝ) ≤ K.edgeSet.ncard := by
      exact_mod_cast copy_edge_ncard_le (SimpleGraph.Copy.ofLE H K hHK)
    simpa only [H.edgeFinset_card, Set.fintypeCard_eq_ncard] using hle.trans hbudget
  have hlocalH : ∀ S : Finset W, S.card = k → (inducedHostEdges H S).card ≤ P * k := by
    intro S hS
    have hInduce : H.induce (S : Set W) ≤ (lowEndpointPrunedGraph K P).induce (S : Set W) :=
      fun _ _ hadj => hH hadj
    rw [inducedHostEdges_card]
    exact (copy_edge_ncard_le (SimpleGraph.Copy.ofLE _ _ hInduce)).trans
      (by simpa only [hS] using lowEndpointPrunedGraph_induced_density K P S)
  obtain ⟨t, ht, hbadCost, hgood⟩ := hdJ d (by omega) U W k a e D P hdk ha hak he hDpos hDpow
    haverage hsizeUpper hlower hupper horient G H J K hHK (P₁ ∪ P₂) G.edgeSet.ncard
    hblocks hhost hlocalH (Nat.cast_nonneg _) hHbudget hclass
  let F := componentModel G t
  let bad := incidenceJointBadSupport G H J K (P₁ ∪ P₂) (nearRegularRepeatThreshold d e)
    (tolerantTupleOrder d) D P a e ((e : ℝ) / 128)
      ((e : ℝ) / 128 * Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) t
  let H₁ := H.deleteEdges (bad : Set (Sym2 W))
  have hsize : F.edgeSet.ncard = e := (mem_componentClass G k e t).mp ht |>.2
  have hFmin : ∀ v, d ≤ F.degree v := fun v => by rw [componentModel_degree_eq]; exact hmin v.val
  have hH₁ : ∀ w, H₁.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE H₁ H (H.deleteEdges_le _)).degree_le w).trans (hhost w)
  have hlocal' : ∀ S : Finset U, S.card ≤ 2 * max (baselineBlockSize d) (nearRegularBlockSize d) →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card := by
    simpa only [max_eq_right hq] using hlocal
  have hrepeat : ∀ f : F.Copy H₁, repeatedEdgeVolume (P₁ ∪ P₂) (copyRawEdges f) <
      3 * nearRegularRepeatThreshold d F.edgeSet.ncard := by
    intro f
    have h := lt_of_not_ge (hgood f).2.1
    simpa only [copyRawEdges_ofLE_comp, hsize] using h
  have hKbudget : (K.edgeFinset.card : ℝ) ≤ M * d * G.edgeSet.ncard := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hbudget
  obtain ⟨marks, hmarkCost, hpoor⟩ := hdB d (by omega) (componentRepresentative G t).supp U W D
    F G H₁ K P₁ P₂ G.edgeSet.ncard (componentModel_connected G t) hFmin hdD hDpow hH₁
    (hP₁.mono hcrossK) (hP₂.mono hcrossK) hdisjoint (Nat.cast_nonneg _) hKbudget hlocal' hrepeat
  refine ⟨J, hJ, hfirst, hsecond, t, ht, bad ∪ marks, blockEdgeUnion (P₁ ∪ P₂), ?_, ?_, ?_⟩
  · intro x y hxy hx hy hremoved
    exact SimpleGraph.deleteEdges_adj.mpr ⟨⟨hxy, Or.inr ⟨hy, hx⟩⟩, hremoved⟩
  · intro g
    have hsum : ((copyRawEdges g ∩ (bad ∪ marks)).card : ℝ) ≤
        (copyRawEdges g ∩ bad).card + (copyRawEdges g ∩ marks).card := by
      exact_mod_cast copy_capacity_union_inter (copyRawEdges g) bad marks
    have hbad : ((copyRawEdges g ∩ bad).card : ℝ) ≤ bad.card := by
      exact_mod_cast Finset.card_le_card (show copyRawEdges g ∩ bad ⊆ bad from Finset.inter_subset_right)
    have hmarks := hmarkCost g
    change (bad.card : ℝ) ≤ (1 / 16 : ℝ) * G.edgeSet.ncard at hbadCost
    linarith only [hsum, hbad, hbadCost, hmarks]
  · intro f havoid
    have hbadAvoid : Disjoint (copyRawEdges f) bad := havoid.mono_right Finset.subset_union_left
    let f₁ := copyIntoDeleteEdges f bad hbadAvoid
    have hmarksAvoid : Disjoint (copyRawEdges f₁) marks := by
      simpa only [f₁, copyRawEdges_copyIntoDeleteEdges] using
        havoid.mono_right (show marks ⊆ bad ∪ marks from Finset.subset_union_right)
    let f₂ := copyIntoDeleteEdges f₁ marks hmarksAvoid
    have hblockLoss : ((copyRawEdges f ∩ blockEdgeUnion (P₁ ∪ P₂)).card : ℝ) ≤
        nearRegularLossFraction 1024 d * F.edgeSet.ncard := by
      simpa only [f₁, f₂, copyRawEdges_ofLE_comp, copyRawEdges_copyIntoDeleteEdges] using hpoor f₂
    have hstar : copyRawEdges f ∉ starImagePatterns H J (copyVertices f) (tolerantTupleOrder d)
        F.edgeSet.ncard D P ((F.edgeSet.ncard : ℝ) / 128 *
          Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) := by
      simpa only [f₁, copyVertices_ofLE_comp, copyRawEdges_ofLE_comp,
        copyVertices_copyIntoDeleteEdges, copyRawEdges_copyIntoDeleteEdges, hsize] using (hgood f₁).2.2
    have hnotOri : copyRawEdges f ∉ orientationPatterns H K P (copyVertices f) a e ((e : ℝ) / 128) := by
      simpa only [f₁, copyVertices_ofLE_comp, copyRawEdges_ofLE_comp,
        copyVertices_copyIntoDeleteEdges, copyRawEdges_copyIntoDeleteEdges] using (hgood f₁).1
    have hBF := componentSide_bipartite G left right hBip t
    have hlow : ((copyRawEdges f ∩ incidentEdgesAtSet H
        (((componentSide G t left).filter (fun v => f v ∉ highHostVertices K P)).image f)).card : ℝ) <
          (e : ℝ) / 128 := by
      apply lt_of_not_ge
      intro hmass
      have hpattern := copy_mem_orientationPatterns F H K f (componentSide G t left) P a
        ((e : ℝ) / 128) (by rw [(hside t ht).1]) hmass
      exact hnotOri (by simpa only [hsize] using hpattern)
    have hcount := incidenceOrientationDefects_card_bound F H f (componentSide G t left)
      (componentSide G t right) (highHostVertices K P) d (fun v _ => hFmin v)
      (fun v hv u hvu => hBF.symm.mem_of_mem_adj hv hvu)
    exact ⟨hblockLoss, by rw [hsize]; linarith only [hcount, hlow], hstar⟩

end Erdos911
