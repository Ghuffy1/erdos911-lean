import Erdos911.PartialLabelMaps

namespace Erdos911

noncomputable def partialLabelTestRows {A C R : Type*} [DecidableEq C]
    (N : R → Finset A) (U : Finset R) (f : A → Option C) : Finset R := by
  classical
  exact if PartialLabelInjective f then U.filter (fun y => ∀ x ∈ N y, f x ≠ none) else ∅

theorem partialLabelTestRows_subset {A C R : Type*} [DecidableEq C]
    (N : R → Finset A) (U : Finset R) (f : A → Option C) : partialLabelTestRows N U f ⊆ U := by
  classical
  intro y hy
  by_cases hf : PartialLabelInjective f
  · exact (Finset.mem_filter.mp (by simpa only [partialLabelTestRows, hf, ite_true] using hy)).1
  · simp only [partialLabelTestRows, hf, ite_false, Finset.notMem_empty] at hy

theorem partialLabelTestRows_info {A C R : Type*} [DecidableEq C]
    (N : R → Finset A) (U : Finset R) (f : A → Option C) (y : R)
    (hy : y ∈ partialLabelTestRows N U f) :
    PartialLabelInjective f ∧ y ∈ U ∧ ∀ x ∈ N y, f x ≠ none := by
  classical
  by_cases hf : PartialLabelInjective f
  · have h := Finset.mem_filter.mp (show y ∈ U.filter (fun y => ∀ x ∈ N y, f x ≠ none) from
      by simpa only [partialLabelTestRows, hf, ite_true] using hy)
    exact ⟨hf, h.1, h.2⟩
  · simp only [partialLabelTestRows, hf, ite_false, Finset.notMem_empty] at hy

theorem partialLabelTestRows_minimum {A C R : Type*} [DecidableEq C]
    (N : R → Finset A) (U : Finset R) (f : A → Option C) (s : ℕ)
    (hmin : ∀ y ∈ U, s ≤ (N y).card) (y : R) (hy : y ∈ partialLabelTestRows N U f) :
    s ≤ (partialLabelRange f (N y)).card := by
  obtain ⟨hf, hyU, hdef⟩ := partialLabelTestRows_info N U f y hy
  rw [partialLabelRange_card f hf (N y) hdef]
  exact hmin y hyU

theorem partialLabelTestRows_restrict {A C R : Type*} [DecidableEq A] [DecidableEq C]
    (N : R → Finset A) (U : Finset R) (S : Finset A) (f : A → C)
    (hf : Set.InjOn f (S : Set A)) :
    partialLabelTestRows N U (restrictPartialLabel S f) = U.filter (fun y => N y ⊆ S) := by
  classical
  rw [partialLabelTestRows, ite_eq_left (restrictPartialLabel_injective S f hf)]
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    intro x hx
    by_contra hn
    exact h x hx (by simp only [restrictPartialLabel, hn, ite_false])
  · rintro ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    intro x hx
    simp only [restrictPartialLabel, h hx, ite_true]
    intro hn
    cases hn

end Erdos911
