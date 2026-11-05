import Erdos911.SequentialWeights
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Option

namespace Erdos911

noncomputable def forestStep {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : Option (Fin n)) (history : Fin n → W) (w : W) : ℝ :=
  match parent with
  | none => 1 / (Fintype.card W : ℝ)
  | some j => if H.Adj (history j) w then 1 / (H.degree (history j) : ℝ) else 0

theorem forestStep_nonneg {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : Option (Fin n)) (history : Fin n → W) (w : W) :
    0 ≤ forestStep H parent history w := by
  cases parent <;> simp only [forestStep]
  · positivity
  · split_ifs <;> positivity

theorem forestStep_sum_le_one {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : Option (Fin n)) (history : Fin n → W) :
    (∑ w, forestStep H parent history w) ≤ 1 := by
  classical
  cases parent with
  | none =>
    simp only [forestStep, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    by_cases hN : Fintype.card W = 0
    · simp [hN]
    · have hNreal : (Fintype.card W : ℝ) ≠ 0 := by exact_mod_cast hN
      simp [hNreal]
  | some j =>
    have hfilter : Finset.univ.filter (H.Adj (history j)) = H.neighborFinset (history j) := by
      ext w
      simp
    have hsum : (∑ w, forestStep H (some j) history w) =
        (H.degree (history j) : ℝ) * (1 / (H.degree (history j) : ℝ)) := by
      simp only [forestStep, ← Finset.sum_filter, hfilter, Finset.sum_const,
        H.card_neighborFinset_eq_degree, nsmul_eq_mul]
    rw [hsum]
    by_cases hd : H.degree (history j) = 0
    · simp [hd]
    · have hdreal : (H.degree (history j) : ℝ) ≠ 0 := by exact_mod_cast hd
      simp [hdreal]

noncomputable def forestAssignmentWeight {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (x : Fin n → W) : ℝ :=
  sequentialWeight (fun i => forestStep H (parent i)) x

theorem forestAssignmentWeight_nonneg {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (x : Fin n → W) :
    0 ≤ forestAssignmentWeight H parent x :=
  sequentialWeight_nonneg _ (fun i => forestStep_nonneg H (parent i)) x

theorem forestAssignmentWeight_sum_le_one {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) :
    (∑ x : Fin n → W, forestAssignmentWeight H parent x) ≤ 1 :=
  sum_sequentialWeight_le_one _ (fun i => forestStep_nonneg H (parent i))
    (fun i => forestStep_sum_le_one H (parent i))

def orderedParent {n : ℕ} (parent : (i : Fin n) → Option (Fin i.val)) (i : Fin n) :
    Option (Fin n) :=
  (parent i).map (fun j => ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩)

def parentFiberCard {n : ℕ} (parent : (i : Fin n) → Option (Fin i.val))
    (q : Option (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i => orderedParent parent i = q)).card

noncomputable def forestDegreeWeight {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ} (x : Fin n → W) :
    Option (Fin n) → ℝ
  | none => 1 / (Fintype.card W : ℝ)
  | some j => 1 / (H.degree (x j) : ℝ)

theorem forestAssignmentWeight_eq_grouped {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (x : Fin n → W)
    (hedges : ∀ i j, parent i = some j → H.Adj (initialSegment x i j) (x i)) :
    forestAssignmentWeight H parent x =
      (1 / (Fintype.card W : ℝ)) ^ parentFiberCard parent none *
        ∏ j, (1 / (H.degree (x j) : ℝ)) ^ parentFiberCard parent (some j) := by
  have hstep : ∀ i, forestStep H (parent i) (initialSegment x i) (x i) =
      forestDegreeWeight H x (orderedParent parent i) := by
    intro i
    cases hp : parent i with
    | none => simp [forestStep, orderedParent, forestDegreeWeight, hp]
    | some j =>
      simp only [forestStep, orderedParent, forestDegreeWeight, hp, Option.map_some]
      rw [ite_eq_left (hedges i j hp)]
      rfl
  rw [forestAssignmentWeight, sequentialWeight_eq_prod]
  simp_rw [hstep]
  rw [← Finset.prod_fiberwise' Finset.univ (orderedParent parent) (forestDegreeWeight H x)]
  simp only [Finset.prod_const, parentFiberCard, Fintype.prod_option, forestDegreeWeight]

theorem parentFiberCard_sum {n : ℕ} (parent : (i : Fin n) → Option (Fin i.val)) :
    (∑ q : Option (Fin n), parentFiberCard parent q) = n := by
  classical
  simp only [parentFiberCard, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem parentFiberCard_root_add_children {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) :
    parentFiberCard parent none + (∑ j : Fin n, parentFiberCard parent (some j)) = n := by
  simpa only [Fintype.sum_option] using parentFiberCard_sum parent

end Erdos911
