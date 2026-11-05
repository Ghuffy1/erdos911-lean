import Erdos911.ConcreteDictionarySelection
import Mathlib.Data.Finset.Option

namespace Erdos911

def PartialLabelInjective {A C : Type*} (f : A → Option C) : Prop :=
  ∀ x y c, f x = some c → f y = some c → x = y

noncomputable def partialLabelRange {A C : Type*} [DecidableEq C]
    (f : A → Option C) (S : Finset A) : Finset C := Finset.eraseNone (S.image f)

theorem mem_partialLabelRange {A C : Type*} [DecidableEq C]
    (f : A → Option C) (S : Finset A) (c : C) :
    c ∈ partialLabelRange f S ↔ ∃ x ∈ S, f x = some c := by
  classical
  simp only [partialLabelRange, Finset.mem_eraseNone, Finset.mem_image]

theorem partialLabelRange_card {A C : Type*} [DecidableEq C]
    (f : A → Option C) (hf : PartialLabelInjective f) (S : Finset A)
    (hdefined : ∀ x ∈ S, f x ≠ none) : (partialLabelRange f S).card = S.card := by
  classical
  have hn : none ∉ S.image f := by
    rintro h
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp h
    exact hdefined x hx heq
  have hinj : Set.InjOn f (S : Set A) := by
    intro x hx y _ heq
    cases hfx : f x with
    | none => exact (hdefined x hx hfx).elim
    | some c => exact hf x y c hfx (heq.symm.trans hfx)
  rw [partialLabelRange, Finset.card_eraseNone_of_not_mem hn]
  exact Finset.card_image_of_injOn hinj

noncomputable def restrictPartialLabel {A C : Type*} [DecidableEq A]
    (S : Finset A) (f : A → C) (x : A) : Option C := if x ∈ S then some (f x) else none

theorem restrictPartialLabel_injective {A C : Type*} [DecidableEq A]
    (S : Finset A) (f : A → C) (hf : Set.InjOn f (S : Set A)) :
    PartialLabelInjective (restrictPartialLabel S f) := by
  intro x y c hx hy
  have hxS : x ∈ S := by
    by_contra hn
    simp only [restrictPartialLabel, hn, ite_false] at hx
    cases hx
  have hyS : y ∈ S := by
    by_contra hn
    simp only [restrictPartialLabel, hn, ite_false] at hy
    cases hy
  have hx' : f x = c := by simpa only [restrictPartialLabel, hxS, ite_true, Option.some.injEq] using hx
  have hy' : f y = c := by simpa only [restrictPartialLabel, hyS, ite_true, Option.some.injEq] using hy
  exact hf hxS hyS (hx'.trans hy'.symm)

theorem partialLabelRange_restrict {A C : Type*} [DecidableEq A] [DecidableEq C]
    (S T : Finset A) (f : A → C) (hTS : T ⊆ S) :
    partialLabelRange (restrictPartialLabel S f) T = T.image f := by
  classical
  ext c
  rw [mem_partialLabelRange, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hxc⟩
    exact ⟨x, hx, by simpa only [restrictPartialLabel, hTS hx, ite_true, Option.some.injEq] using hxc⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp only [restrictPartialLabel, hTS hx, ite_true]⟩

end Erdos911
