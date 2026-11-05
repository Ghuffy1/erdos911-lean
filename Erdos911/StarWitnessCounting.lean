import Erdos911.GraphCounting
import Mathlib.Data.Fintype.BigOperators

namespace Erdos911

def twoStepNeighbors {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W) : Finset W :=
  (H.neighborFinset v).biUnion (fun z => H.neighborFinset z)

theorem mem_twoStepNeighbors {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v w : W) :
    w ∈ twoStepNeighbors H v ↔ ∃ z, H.Adj v z ∧ H.Adj z w := by
  simp only [twoStepNeighbors, Finset.mem_biUnion, SimpleGraph.mem_neighborFinset]

theorem twoStepNeighbors_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ w, H.degree w ≤ D) (v : W) : (twoStepNeighbors H v).card ≤ D ^ 2 := by
  calc
    (twoStepNeighbors H v).card ≤ ∑ z ∈ H.neighborFinset v, (H.neighborFinset z).card :=
      Finset.card_biUnion_le
    _ = ∑ z ∈ H.neighborFinset v, H.degree z := by simp
    _ ≤ ∑ _z ∈ H.neighborFinset v, D := Finset.sum_le_sum (fun z _ => hD z)
    _ = H.degree v * D := by simp
    _ ≤ D * D := Nat.mul_le_mul_right D (hD v)
    _ = D ^ 2 := (pow_two D).symm

def optionalTwoStepNeighbors {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W) : Finset (Option W) :=
  insert none ((twoStepNeighbors H v).image some)

theorem optionalTwoStepNeighbors_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ w, H.degree w ≤ D) (v : W) :
    (optionalTwoStepNeighbors H v).card ≤ D ^ 2 + 1 := by
  calc
    (optionalTwoStepNeighbors H v).card ≤ ((twoStepNeighbors H v).image some).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (twoStepNeighbors H v).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ D ^ 2 + 1 := Nat.add_le_add_right (twoStepNeighbors_card_le H D hD v) 1

def starWitnessTuples {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (v : W) (s : ℕ) :
    Finset (Fin s → Option W) := Fintype.piFinset (fun _ => optionalTwoStepNeighbors H v)

theorem starWitnessTuples_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ w, H.degree w ≤ D) (v : W) (s : ℕ) :
    (starWitnessTuples H v s).card ≤ (D ^ 2 + 1) ^ s := by
  rw [starWitnessTuples, Fintype.card_piFinset_const]
  exact Nat.pow_le_pow_left (optionalTwoStepNeighbors_card_le H D hD v) s

/-- Padding a witness with `none` also permits inactive roles and shorter
tuples. The bound is uniform over the chosen image support. -/
theorem starWitnessConfigurations_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ w, H.degree w ≤ D) (U : Finset W) (s : ℕ) :
    (Fintype.piFinset (fun v : U => starWitnessTuples H v.val s)).card ≤
      (D ^ 2 + 1) ^ (s * U.card) := by
  rw [Fintype.card_piFinset]
  calc
    (∏ v : U, (starWitnessTuples H v.val s).card) ≤ ∏ _v : U, (D ^ 2 + 1) ^ s :=
      Finset.prod_le_prod (fun v _ => starWitnessTuples_card_le H D hD v.val s)
    _ = (D ^ 2 + 1) ^ (s * U.card) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← pow_mul]

end Erdos911
