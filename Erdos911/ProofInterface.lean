import Erdos911.Quantifiers
import Erdos911.HostObstruction

open Filter SimpleGraph

namespace Erdos911

/-- The complete combinatorial obligation left by the reductions below.
This file defines the obligation and proves equivalences. It does not assert it. -/
def UniformAvoidance : Prop :=
  ∀ k : ℕ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
    C * n ≤ (G.edgeSet.ncard : ℝ) →
      ∀ (m : ℕ) (F : SimpleGraph (Fin m)),
        (F.edgeSet.ncard : ℝ) ≤ (k : ℝ) * C * G.edgeSet.ncard →
          ∃ (R : SimpleGraph (Fin m)), R ≤ F ∧
            ¬G.IsContained R ∧ ¬G.IsContained (F \ R)

theorem fixedMultipliers_iff_uniformAvoidance :
    FixedMultiplierStatement ↔ UniformAvoidance := by
  constructor
  · intro h k
    obtain ⟨C₀, hC₀⟩ := h k
    refine ⟨C₀, ?_⟩
    intro C hC n G hn hedges
    exact (sizeRamsey_real_gt_iff G G ((k : ℝ) * C * G.edgeSet.ncard)).mp
      (hC₀ C hC n G hn hedges)
  · intro h k
    obtain ⟨C₀, hC₀⟩ := h k
    refine ⟨C₀, ?_⟩
    intro C hC n G hn hedges
    exact (sizeRamsey_real_gt_iff G G ((k : ℝ) * C * G.edgeSet.ncard)).mpr
      (hC₀ C hC n G hn hedges)

theorem exact_iff_uniformAvoidance : ExactStatement ↔ UniformAvoidance :=
  exact_iff_fixedMultipliers.trans fixedMultipliers_iff_uniformAvoidance

/-- A literal restatement for comparison with the pinned source declaration. -/
theorem exact_statement_alignment : ExactStatement ↔
    ∃ f : ℝ → ℝ, Tendsto (fun x ↦ f x / x) atTop atTop ∧
      ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
        C * n ≤ (G.edgeSet.ncard : ℝ) →
          f C * G.edgeSet.ncard < (sizeRamsey G G : ℝ) := Iff.rfl

end Erdos911
