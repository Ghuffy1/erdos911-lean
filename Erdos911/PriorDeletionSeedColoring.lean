import Erdos911.SeedMatchingColoring

namespace Erdos911

/-- Earlier deletions restrict which copies need a seed certificate.
The candidate lists continue to use the original ambient graphs. -/
theorem no_copy_of_seed_events_after_deletions {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s r : ℕ) (τ T u : ℝ) (hτ : 0 < τ) (P : Finset (Sym2 W))
    (C : Finset (SeedDescription F H s)) (B : I → Finset W) (h : ℕ)
    (marks : (Fin h × I) → Bool)
    (hmarks : ∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B h u)
    (hcertificate : ∀ f : F.Copy H, Disjoint (copyRawEdges f) P → ∃ c ∈ C, ∃ E : Finset V,
      (E.card : ℝ) ≤ u ∧ ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v) :
    ¬F.IsContained (H.deleteEdges
      ((P ∪ incidentEdgesAtSet H (roundMarkedVertices B h marks) : Finset (Sym2 W)) : Set (Sym2 W))) := by
  rintro ⟨f⟩
  let fH := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
  have hdisjoint := copy_deleteEdges_disjoint F H
    (P ∪ incidentEdgesAtSet H (roundMarkedVertices B h marks)) f
  obtain ⟨hprior, hstars⟩ := Finset.disjoint_union_right.mp hdisjoint
  obtain ⟨c, hc, E, hE, htrue⟩ := hcertificate fH hprior
  exact hmarks ⟨c, hc⟩ (seeded_copy_thickMatchingEvent F H J fH s r τ T u hτ c B h marks
    hstars E hE htrue)

/-- The blue capacity is the sum of the prior-deletion allowance and
the marked-star allowance, evaluated on copies in the original host. -/
theorem seed_matching_coloring_after_deletions {V U W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (G : SimpleGraph U) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hFG : F.IsContained G) (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ)
    (s r h : ℕ) (τ T u prior budget : ℝ) (hτ : 0 < τ) (P : Finset (Sym2 W))
    (C : Finset (SeedDescription F H s)) (B : I → Finset W)
    (hmarks : ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B h u) ∧
      (∑ e, if marks e = true then ((B e.2).card : ℝ) else 0) ≤ budget)
    (hcertificate : ∀ f : F.Copy H, Disjoint (copyRawEdges f) P → ∃ c ∈ C, ∃ E : Finset V,
      (E.card : ℝ) ≤ u ∧ ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v)
    (hprior : ∀ f : G.Copy H, ((copyRawEdges f ∩ P).card : ℝ) ≤ prior)
    (hbudget : prior + budget * Δ < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  obtain ⟨marks, havoid, hcost⟩ := hmarks
  let S := incidentEdgesAtSet H (roundMarkedVertices B h marks)
  have hred : ¬F.IsContained (H.deleteEdges ((P ∪ S : Finset (Sym2 W)) : Set (Sym2 W))) :=
    no_copy_of_seed_events_after_deletions F H J s r τ T u hτ P C B h marks havoid hcertificate
  have hcapacity (f : G.Copy H) : (copyRawEdges f ∩ (P ∪ S)).card < G.edgeSet.ncard := by
    have hcap := markedVertexUnion_copy_capacity G H f (fun e : Fin h × I => B e.2) marks Δ hΔ
    have hsum : (∑ e, if marks e = true then (B e.2).card * (Δ : ℝ) else 0) =
        (∑ e, if marks e = true then ((B e.2).card : ℝ) else 0) * Δ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    rw [hsum] at hcap
    have hstars : ((copyRawEdges f ∩ S).card : ℝ) ≤ budget * Δ :=
      hcap.trans (mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg Δ))
    have hunion : ((copyRawEdges f ∩ (P ∪ S)).card : ℝ) ≤
        (copyRawEdges f ∩ P).card + (copyRawEdges f ∩ S).card := by
      exact_mod_cast copy_capacity_union_inter (copyRawEdges f) P S
    have hlt := (hunion.trans (add_le_add (hprior f) hstars)).trans_lt hbudget
    exact_mod_cast hlt
  exact avoiding_coloring_of_deleted_capacity F G H hFG (P ∪ S) hred hcapacity

end Erdos911
