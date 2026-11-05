import Erdos911.PartialLabelMaps
import Erdos911.SmallCoordinateSets

namespace Erdos911

noncomputable def optionTupleRange {A : Type*} [DecidableEq A]
    (q : ℕ) (f : Fin q → Option A) : Finset A := partialLabelRange f Finset.univ

/-- Every set with at most q elements is the range of a q-tuple with
an optional entry used for padding. -/
theorem exists_option_tuple_range {A : Type*} [DecidableEq A]
    (S : Finset A) (q : ℕ) (hS : S.card ≤ q) :
    ∃ f : Fin q → Option A, optionTupleRange q f = S := by
  classical
  let f : Fin q → Option A := fun i =>
    if hi : i.val < S.card then some (S.equivFin.symm ⟨i.val, hi⟩).val else none
  refine ⟨f, ?_⟩
  ext a
  rw [optionTupleRange, mem_partialLabelRange]
  constructor
  · rintro ⟨i, _, hi⟩
    by_cases his : i.val < S.card
    · have heq : (S.equivFin.symm ⟨i.val, his⟩).val = a := by
        simpa only [f, his, dite_true, Option.some.injEq] using hi
      exact heq ▸ (S.equivFin.symm ⟨i.val, his⟩).property
    · simp only [f, his, dite_false] at hi
      cases hi
  · intro ha
    let i : Fin S.card := S.equivFin ⟨a, ha⟩
    let j : Fin q := ⟨i.val, lt_of_lt_of_le i.isLt hS⟩
    refine ⟨j, Finset.mem_univ _, ?_⟩
    have hj : j.val < S.card := i.isLt
    have hback : S.equivFin.symm i = (⟨a, ha⟩ : ↥S) := Equiv.symm_apply_apply S.equivFin _
    have hji : (⟨j.val, hj⟩ : Fin S.card) = i := rfl
    change (if h : j.val < S.card then some (S.equivFin.symm ⟨j.val, h⟩).val else none) = some a
    rw [dite_eq_left hj, hji, hback]

/-- The number of possible patterns of size at most q on A is at most
(|A|+1)^q, without an additional multiplicative factor q+1. -/
theorem small_patterns_card_bound (A : Type*) [Fintype A] [DecidableEq A] (q : ℕ) :
    (smallCoordinateSets A q).card ≤ (Fintype.card A + 1) ^ q := by
  classical
  have hsub : smallCoordinateSets A q ⊆
      (Finset.univ : Finset (Fin q → Option A)).image (optionTupleRange q) := by
    intro S hS
    obtain ⟨f, hf⟩ := exists_option_tuple_range S q (Finset.mem_filter.mp hS).2
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, hf⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_fin] using hc

theorem row_pattern_image_card_bound {A R : Type*} [Fintype A] [DecidableEq A]
    (N : R → Finset A) (T : Finset R) (q a : ℕ)
    (hN : ∀ y ∈ T, (N y).card ≤ q) (hA : Fintype.card A ≤ a) :
    (T.image N).card ≤ (a + 1) ^ q := by
  classical
  have hsub : T.image N ⊆ smallCoordinateSets A q := by
    intro S hS
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN y hy⟩
  exact ((Finset.card_le_card hsub).trans (small_patterns_card_bound A q)).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hA 1) q)

end Erdos911
