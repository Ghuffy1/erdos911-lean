import Erdos911.SizeRamsey
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
Finite counterexamples to two auxiliary statements as printed in the manuscript.
These concern missing parameter hypotheses, not the assertion of problem 911.
-/

namespace Erdos911.AuxiliaryCounterexamples

def disjointStars : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun v w =>
    (v = 0 ∧ (w = 2 ∨ w = 3)) ∨ (v = 1 ∧ (w = 4 ∨ w = 5))

instance : DecidableRel disjointStars.Adj := by
  unfold disjointStars
  infer_instance

def starCenters : Finset (Fin 6) := {0, 1}

def commonNeighbors (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (S : Finset (Fin 6)) : Finset (Fin 6) :=
  Finset.univ.filter fun v => ∀ w ∈ S, G.Adj v w

/-- Every subset of the two centers with at most one member has more than one
common neighbor, while the two centers together have none. -/
theorem centers_s_one_witness :
    (∀ v ∈ starCenters, disjointStars.degree v ≤ 2) ∧
    (∀ S : Finset (Fin 6), S ⊆ starCenters → S.card ≤ 1 →
      1 < (commonNeighbors disjointStars S).card) ∧
    starCenters.card = 2 ∧
    (commonNeighbors disjointStars starCenters).card = 0 := by
  decide

/-- At s = 1, the displayed expression log(2D/T)/(s-1) is zero in Lean.
This identity applies to any real numerator, including that logarithm. -/
theorem centers_s_one_parameter (r : ℝ) : r / ((1 : ℝ) - 1) = 0 := by simp

def denseCodegreeGraph : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel fun v w =>
    6 < (((⊤ : SimpleGraph (Fin 9)).neighborFinset v) ∩
      ((⊤ : SimpleGraph (Fin 9)).neighborFinset w)).card

instance : DecidableRel denseCodegreeGraph.Adj := by
  unfold denseCodegreeGraph
  infer_instance

/-- K₉ has maximum degree 8, and its graph of codegrees greater than 6
also has degree 8. These exceed q = 5 despite T' = 6 > q. -/
theorem codegree_parameters :
    (5 : ℚ) < 6 ∧ (1 / 10 : ℚ) < (6 - 5) / 8 ∧
    (∀ v : Fin 9, (⊤ : SimpleGraph (Fin 9)).degree v = 8) ∧
    (∀ v : Fin 9, denseCodegreeGraph.degree v = 8) := by
  constructor
  · norm_num
  constructor
  · norm_num
  decide

/-- There cannot be two disjoint 5-element sets in the 9-vertex host,
irrespective of the cross density. -/
theorem no_disjoint_five_sets (S T : Finset (Fin 9))
    (hS : S.card = 5) (hT : T.card = 5) : ¬Disjoint S T := by
  intro hdis
  have hcard := Finset.card_le_card (Finset.subset_univ (S ∪ T))
  rw [Finset.card_union_of_disjoint hdis, hS, hT] at hcard
  norm_num at hcard

end Erdos911.AuxiliaryCounterexamples
