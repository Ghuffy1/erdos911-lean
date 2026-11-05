import Erdos911.SeedMatchingObstruction
import Erdos911.NeighborhoodSeedMarking
import Erdos911.DeletedEdgeCapacity

namespace Erdos911

/-- A seed-event marking with a bounded vertex cost gives an actual
two-coloring once every red test copy supplies its sampled certificate. -/
theorem seed_matching_avoiding_coloring {V U W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (G : SimpleGraph U) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hFG : F.IsContained G) (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ)
    (s r h : ℕ) (τ T u budget : ℝ) (hτ : 0 < τ)
    (C : Finset (SeedDescription F H s)) (B : I → Finset W)
    (hmarks : ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B h u) ∧
      (∑ e, if marks e = true then ((B e.2).card : ℝ) else 0) ≤ budget)
    (hcertificate : ∀ f : F.Copy H, ∃ c ∈ C, ∃ E : Finset V,
      (E.card : ℝ) ≤ u ∧ ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v)
    (hbudget : budget * Δ < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  obtain ⟨marks, havoid, hcost⟩ := hmarks
  let K := incidentEdgesAtSet H (roundMarkedVertices B h marks)
  have hred : ¬F.IsContained (H.deleteEdges (K : Set (Sym2 W))) :=
    no_copy_of_seed_matching_events F H J s r τ T u hτ C B h marks havoid hcertificate
  have hcapacity (f : G.Copy H) : (copyRawEdges f ∩ K).card < G.edgeSet.ncard := by
    have hcap := markedVertexUnion_copy_capacity G H f (fun e : Fin h × I => B e.2) marks Δ hΔ
    have hsum : (∑ e, if marks e = true then (B e.2).card * (Δ : ℝ) else 0) =
        (∑ e, if marks e = true then ((B e.2).card : ℝ) else 0) * Δ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    rw [hsum] at hcap
    have hlt := (hcap.trans (mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg Δ))).trans_lt hbudget
    exact_mod_cast hlt
  exact avoiding_coloring_of_deleted_capacity F G H hFG K hred hcapacity

end Erdos911
