import Erdos911.PriorDeletionSeedColoring

namespace Erdos911

theorem incidentEdgesAtSet_mono {W : Type*} [Fintype W] [DecidableEq W]
    {H K : SimpleGraph W} [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (S : Finset W) : incidentEdgesAtSet H S ⊆ incidentEdgesAtSet K S := by
  intro e he
  obtain ⟨heH, hincident⟩ := (mem_incidentEdgesAtSet_iff H S e).mp he
  exact (mem_incidentEdgesAtSet_iff K S e).mpr
    ⟨SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hHK (SimpleGraph.mem_edgeFinset.mp heH)), hincident⟩

/-- The initial host deletions, prior copy pruning, and marked stars all
contribute to one capacity bound on copies in the original host. -/
theorem seed_matching_coloring_after_deletions_ambient {V U W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (G : SimpleGraph U) [DecidableRel G.Adj]
    (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hHK : H ≤ K) (hFG : F.IsContained G) (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ)
    (s r h : ℕ) (τ T u initial prior budget : ℝ) (hτ : 0 < τ) (P : Finset (Sym2 W))
    (C : Finset (SeedDescription F H s)) (B : I → Finset W)
    (hmarks : ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B h u) ∧
      (∑ e, if marks e = true then ((B e.2).card : ℝ) else 0) ≤ budget)
    (hcertificate : ∀ f : F.Copy H, Disjoint (copyRawEdges f) P → ∃ c ∈ C, ∃ E : Finset V,
      (E.card : ℝ) ≤ u ∧ ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v)
    (hinitial : ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ initial)
    (hprior : ∀ f : G.Copy K, ((copyRawEdges f ∩ P).card : ℝ) ≤ prior)
    (hbudget : initial + prior + budget * Δ < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  obtain ⟨marks, havoid, hcost⟩ := hmarks
  let S := incidentEdgesAtSet H (roundMarkedVertices B h marks)
  let D := (K \ H).edgeFinset ∪ (P ∪ S)
  have hredH : ¬F.IsContained (H.deleteEdges ((P ∪ S : Finset (Sym2 W)) : Set (Sym2 W))) :=
    no_copy_of_seed_events_after_deletions F H J s r τ T u hτ P C B h marks havoid hcertificate
  have hkeep : K.deleteEdges (D : Set (Sym2 W)) ≤
      H.deleteEdges ((P ∪ S : Finset (Sym2 W)) : Set (Sym2 W)) := by
    intro v w hvw
    obtain ⟨hK, hD⟩ := SimpleGraph.deleteEdges_adj.mp hvw
    have hH : H.Adj v w := by
      by_contra hn
      exact hD (Finset.mem_union_left _ (SimpleGraph.mem_edgeFinset.mpr ⟨hK, hn⟩))
    exact SimpleGraph.deleteEdges_adj.mpr
      ⟨hH, fun he => hD (Finset.mem_union_right _ he)⟩
  have hred : ¬F.IsContained (K.deleteEdges (D : Set (Sym2 W))) :=
    fun hf => hredH (hf.trans ⟨SimpleGraph.Copy.ofLE _ _ hkeep⟩)
  have hcapacity (f : G.Copy K) : (copyRawEdges f ∩ D).card < G.edgeSet.ncard := by
    have hcap := markedVertexUnion_copy_capacity G K f (fun e : Fin h × I => B e.2) marks Δ hΔ
    have hsum : (∑ e, if marks e = true then (B e.2).card * (Δ : ℝ) else 0) =
        (∑ e, if marks e = true then ((B e.2).card : ℝ) else 0) * Δ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    rw [hsum] at hcap
    have hstars : ((copyRawEdges f ∩ S).card : ℝ) ≤ budget * Δ := by
      have hsub : copyRawEdges f ∩ S ⊆ copyRawEdges f ∩
          incidentEdgesAtSet K (roundMarkedVertices B h marks) :=
        Finset.inter_subset_inter_left (incidentEdgesAtSet_mono hHK _)
      have hcard : ((copyRawEdges f ∩ S).card : ℝ) ≤
          (copyRawEdges f ∩ incidentEdgesAtSet K (roundMarkedVertices B h marks)).card := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (hcap.trans (mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg Δ)))
    have hpriorStars : ((copyRawEdges f ∩ (P ∪ S)).card : ℝ) ≤
        (copyRawEdges f ∩ P).card + (copyRawEdges f ∩ S).card := by
      exact_mod_cast copy_capacity_union_inter (copyRawEdges f) P S
    have htotal : ((copyRawEdges f ∩ D).card : ℝ) ≤
        (copyRawEdges f ∩ (K \ H).edgeFinset).card + (copyRawEdges f ∩ (P ∪ S)).card := by
      exact_mod_cast copy_capacity_union_inter (copyRawEdges f) (K \ H).edgeFinset (P ∪ S)
    have hlt : ((copyRawEdges f ∩ D).card : ℝ) < G.edgeSet.ncard := by
      linarith only [htotal, hpriorStars, hinitial f, hprior f, hstars, hbudget]
    exact_mod_cast hlt
  exact avoiding_coloring_of_deleted_capacity F G K hFG D hred hcapacity

end Erdos911
