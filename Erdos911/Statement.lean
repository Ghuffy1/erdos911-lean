import Erdos911.SizeRamsey
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter SimpleGraph

namespace Erdos911

/-- The proposition of Formal Conjectures problem 911, copied without change. -/
def ExactStatement : Prop :=
    ∃ f : ℝ → ℝ, Tendsto (fun x ↦ f x / x) atTop atTop ∧
      ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
        C * n ≤ (G.edgeSet.ncard : ℝ) →
          f C * G.edgeSet.ncard < (sizeRamsey G G : ℝ)

/-- The fixed-integer-multiplier formulation used to assemble the manuscript.
This is a proposition to be proved, not an assumption or an axiom. -/
def FixedMultiplierStatement : Prop :=
    ∀ k : ℕ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      C * n ≤ (G.edgeSet.ncard : ℝ) →
        (k : ℝ) * C * G.edgeSet.ncard < (sizeRamsey G G : ℝ)

end Erdos911
