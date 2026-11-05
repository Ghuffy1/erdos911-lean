import Erdos911.NearRegularJointPruning
import Erdos911.NearRegularBlockPruning
import Erdos911.NearRegularBlockExtraction
import Erdos911.CopyDeletionLifts
import Erdos911.DeletedEdgeCapacity
import Erdos911.DenseWitnessBound

namespace Erdos911

/-- Joint type pruning and block marking supply the two actual-copy
conditions used by the near-regular seed certificates. All certificates
refer to the same residual graph chosen before either deletion. -/
theorem near_regular_prior_pruning_ambient (A M C : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D Δ : ℕ) (G : SimpleGraph U) [DecidableRel G.Adj]
      (K H : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj],
    H ≤ K → (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ Δ) →
    (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
    d ≤ D → D ≤ d ^ 3 → (∀ w, H.degree w ≤ D) →
    16 * M * d * Δ ≤ (D : ℝ) → (D : ℝ) ≤ 32 * M * d * Δ →
    (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard →
    (∀ S : Finset U, S.card ≤ 2 * nearRegularBlockSize d →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
    ∀ k a : ℕ, Real.exp ((a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
      ((componentClass G k a).card : ℝ) →
    ∃ J : SimpleGraph W, letI : DecidableRel J.Adj := Classical.decRel J.Adj
      J ≤ H ∧
      (∀ X Y : Finset W, X.card = baselineBlockSize d → Y.card = baselineBlockSize d →
        Disjoint X Y → (crossEdges J X Y : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) ∧
      (∀ X Y : Finset W, X.card = nearRegularBlockSize d → Y.card = nearRegularBlockSize d →
        Disjoint X Y → (crossEdges J X Y : ℝ) ≤
          nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) ∧
      ∃ t ∈ componentClass G k a, ∃ P : Finset (Sym2 W),
        (∀ g : G.Copy K, ((copyRawEdges g ∩ P).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 8) ∧
        ∀ f : (componentModel G t).Copy H, Disjoint (copyRawEdges f) P →
          (¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) (tolerantTupleOrder d) D
            (((componentModel G t).edgeSet.ncard : ℝ) / 32 *
              Real.log ((D : ℝ) / nearRegularCommonCutoff D d))) ∧
          (((componentModel G t) \ copyRetainedGraph J f).edgeSet.ncard : ℝ) ≤
            nearRegularLossFraction 1024 d * (componentModel G t).edgeSet.ncard := by
  classical
  obtain ⟨dJ, hdJ⟩ := near_regular_joint_pruning A M hA hM
  obtain ⟨dB, hdB⟩ := near_regular_block_pruning M C hC
  obtain ⟨dQ, hdQ⟩ := near_regular_block_sizes_ordered_uniform
  refine ⟨max 2 (max dJ (max dB dQ)), ?_⟩
  intro d hd U W _ _ _ _ D Δ G _ K H _ _ hHK hmin hmax hdegree hdD hDpow hhost hlower hupper
    hbudget hlocal k a hclass
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hDpos : 0 < D := by omega
  have hq := hdQ d (by omega)
  have hρ : 0 ≤ nearRegularRectangleDensity d := by unfold nearRegularRectangleDensity; positivity
  obtain ⟨P₁, P₂, hP₁, hP₂, hcross, hblocks, hfirst, hsecond⟩ :=
    exists_two_scale_residual_blocks H (baselineBlockSize d) (nearRegularBlockSize d)
      (1 / 4) (nearRegularRectangleDensity d) (by norm_num) hρ hq
  let J := blockResidual H (P₁ ∪ P₂)
  have hclasspos : (componentClass G k a).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.exp_pos _).trans_le hclass
  obtain ⟨t₀, ht₀⟩ := hclasspos
  obtain ⟨horder₀, hsize₀⟩ := (mem_componentClass G k a t₀).mp ht₀
  have hmin₀ : ∀ v, d ≤ (componentModel G t₀).degree v := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using (componentModel_degree_bounds G d Δ hmin hmax t₀ v).1
  have hmax₀ : ∀ v, (componentModel G t₀).degree v ≤ Δ := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using (componentModel_degree_bounds G d Δ hmin hmax t₀ v).2
  have hcard₀ : Fintype.card (componentRepresentative G t₀).supp = k := by
    simpa only [componentOrder, Nat.card_eq_fintype_card] using horder₀
  obtain ⟨v₀⟩ := (componentModel_connected G t₀).nonempty
  have hdk : d ≤ k := by
    rw [← hcard₀]
    exact (hmin₀ v₀).trans ((componentModel G t₀).degree_lt_card_verts v₀).le
  have ha : 0 < a := by
    rw [← hsize₀]
    exact componentSize_pos G (fun v => (show 1 ≤ d by omega).trans (hmin v)) t₀
  have haverage : (d : ℝ) * k ≤ 2 * a := by
    have h := component_degree_sum_bound G d hmin t₀
    rw [horder₀, hsize₀] at h
    exact_mod_cast h
  have hsizeUpper : 2 * (a : ℝ) ≤ (Δ : ℝ) * k := by
    have h := (degree_edge_count_bounds (componentModel G t₀) d Δ hmin₀ hmax₀).2
    change (componentSize G t₀ : ℝ) ≤ (Δ : ℝ) * Fintype.card (componentRepresentative G t₀).supp / 2 at h
    rw [hsize₀, hcard₀] at h
    linarith only [h]
  have hbudget' : (K.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hbudget
  have hHbudget : (H.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    have hle : (H.edgeSet.ncard : ℝ) ≤ K.edgeSet.ncard := by
      exact_mod_cast copy_edge_ncard_le (SimpleGraph.Copy.ofLE H K hHK)
    simpa only [H.edgeFinset_card, Set.fintypeCard_eq_ncard] using hle.trans hbudget
  obtain ⟨t, ht, hbadCost, hgood⟩ := hdJ d (by omega) U W k a D Δ hdk ha hDpos hDpow
    haverage hsizeUpper hdegree hlower hupper G H J (P₁ ∪ P₂) G.edgeSet.ncard hblocks hhost
    (Nat.cast_nonneg _) hHbudget hclass
  let F := componentModel G t
  let bad := jointBadSupport G H J (P₁ ∪ P₂) (nearRegularRepeatThreshold d a)
    (tolerantTupleOrder d) D ((a : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d)) t
  let H₁ := H.deleteEdges (bad : Set (Sym2 W))
  have hsize : F.edgeSet.ncard = a := (mem_componentClass G k a t).mp ht |>.2
  have hFmin : ∀ v, d ≤ F.degree v := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using (componentModel_degree_bounds G d Δ hmin hmax t v).1
  have hH₁ : ∀ w, H₁.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE H₁ H (H.deleteEdges_le _)).degree_le w).trans (hhost w)
  have hlocal' : ∀ S : Finset U, S.card ≤ 2 * max (baselineBlockSize d) (nearRegularBlockSize d) →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card := by
    simpa only [max_eq_right hq] using hlocal
  have hrepeat : ∀ f : F.Copy H₁, repeatedEdgeVolume (P₁ ∪ P₂) (copyRawEdges f) <
      3 * nearRegularRepeatThreshold d F.edgeSet.ncard := by
    intro f
    have h := lt_of_not_ge (hgood f).1
    simpa only [copyRawEdges_ofLE_comp, hsize] using h
  obtain ⟨marks, hmarkCost, hpoor⟩ := hdB d (by omega) (componentRepresentative G t).supp U W D
    F G H₁ K P₁ P₂ G.edgeSet.ncard (componentModel_connected G t) hFmin hdD hDpow hH₁
    (hP₁.mono hHK) (hP₂.mono hHK) hcross (Nat.cast_nonneg _) hbudget' hlocal' hrepeat
  refine ⟨J, blockResidual_le H _, hfirst, hsecond, t, ht, bad ∪ marks, ?_, ?_⟩
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
    have hstar := (hgood f₁).2
    have hblockLoss : ((copyRawEdges f ∩ blockEdgeUnion (P₁ ∪ P₂)).card : ℝ) ≤
        nearRegularLossFraction 1024 d * F.edgeSet.ncard := by
      simpa only [f₁, f₂, copyRawEdges_ofLE_comp, copyRawEdges_copyIntoDeleteEdges] using hpoor f₂
    have hmissing := copy_missing_edges_le J f (blockEdgeUnion (P₁ ∪ P₂)) (by
      intro u v huv hn
      exact SimpleGraph.deleteEdges_adj.mpr ⟨huv, hn⟩)
    have hmissingReal : ((F \ copyRetainedGraph J f).edgeSet.ncard : ℝ) ≤
        (copyRawEdges f ∩ blockEdgeUnion (P₁ ∪ P₂)).card := by
      rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at hmissing
      exact_mod_cast hmissing
    refine ⟨?_, hmissingReal.trans hblockLoss⟩
    have hsize' : (componentModel G t).edgeSet.ncard = a := hsize
    simpa only [f₁, copyVertices_ofLE_comp, copyRawEdges_ofLE_comp,
      copyVertices_copyIntoDeleteEdges, copyRawEdges_copyIntoDeleteEdges, hsize'] using hstar

theorem near_regular_prior_pruning (A M C : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D Δ : ℕ) (G : SimpleGraph U) [DecidableRel G.Adj]
      (H : SimpleGraph W) [DecidableRel H.Adj],
    (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ Δ) →
    (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
    d ≤ D → D ≤ d ^ 3 → (∀ w, H.degree w ≤ D) →
    16 * M * d * Δ ≤ (D : ℝ) → (D : ℝ) ≤ 32 * M * d * Δ →
    (H.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard →
    (∀ S : Finset U, S.card ≤ 2 * nearRegularBlockSize d →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
    ∀ k a : ℕ, Real.exp ((a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
      ((componentClass G k a).card : ℝ) →
    ∃ J : SimpleGraph W, letI : DecidableRel J.Adj := Classical.decRel J.Adj
      J ≤ H ∧
      (∀ X Y : Finset W, X.card = baselineBlockSize d → Y.card = baselineBlockSize d →
        Disjoint X Y → (crossEdges J X Y : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) ∧
      (∀ X Y : Finset W, X.card = nearRegularBlockSize d → Y.card = nearRegularBlockSize d →
        Disjoint X Y → (crossEdges J X Y : ℝ) ≤
          nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) ∧
      ∃ t ∈ componentClass G k a, ∃ P : Finset (Sym2 W),
        (∀ g : G.Copy H, ((copyRawEdges g ∩ P).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 8) ∧
        ∀ f : (componentModel G t).Copy H, Disjoint (copyRawEdges f) P →
          (¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) (tolerantTupleOrder d) D
            (((componentModel G t).edgeSet.ncard : ℝ) / 32 *
              Real.log ((D : ℝ) / nearRegularCommonCutoff D d))) ∧
          (((componentModel G t) \ copyRetainedGraph J f).edgeSet.ncard : ℝ) ≤
            nearRegularLossFraction 1024 d * (componentModel G t).edgeSet.ncard := by
  obtain ⟨d₀, hd₀⟩ := near_regular_prior_pruning_ambient A M C hA hM hC
  refine ⟨d₀, ?_⟩
  intro d hd U W _ _ _ _ D Δ G _ H _ hmin hmax hdegree hdD hDpow hhost hlower hupper
    hbudget hlocal k a hclass
  exact hd₀ d hd U W D Δ G H H le_rfl hmin hmax hdegree hdD hDpow hhost hlower hupper
    hbudget hlocal k a hclass

end Erdos911
