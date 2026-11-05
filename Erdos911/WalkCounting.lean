import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos911

/-- A prescribed start and end have at most D^l walks of length l in a
graph whose degrees are bounded by D. -/
theorem walk_count_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (l : ℕ) (u v : V) :
    (G.finsetWalkLength l u v).card ≤ D ^ l := by
  induction l generalizing u v with
  | zero =>
    by_cases h : u = v
    · subst v
      simp [SimpleGraph.finsetWalkLength]
    · simp [SimpleGraph.finsetWalkLength, h]
  | succ l ih =>
    rw [SimpleGraph.finsetWalkLength]
    apply le_trans Finset.card_biUnion_le
    calc
      _ ≤ ∑ _w : G.neighborSet u, D ^ l := by
        apply Finset.sum_le_sum
        intro w _
        rw [Finset.card_map]
        exact ih w.val v
      _ = G.degree u * D ^ l := by
        simp [G.card_neighborSet_eq_degree]
      _ ≤ D * D ^ l := Nat.mul_le_mul_right _ (hD u)
      _ = D ^ (l + 1) := by rw [pow_succ, Nat.mul_comm]

end Erdos911
