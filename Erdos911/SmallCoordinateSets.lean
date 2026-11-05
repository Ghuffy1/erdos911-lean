import Erdos911.DictionaryParameters
import Mathlib.Data.Nat.Choose.Bounds

namespace Erdos911

noncomputable def smallCoordinateSets (C : Type*) [Fintype C] (J : ℕ) : Finset (Finset C) := by
  classical
  exact Finset.univ.filter (fun S => S.card ≤ J)

theorem smallCoordinateSets_card_le (C : Type*) [Fintype C] [DecidableEq C] (J : ℕ)
    (hC : 1 ≤ Fintype.card C) :
    (smallCoordinateSets C J).card ≤ (J + 1) * Fintype.card C ^ J := by
  classical
  have hsub : smallCoordinateSets C J ⊆
      (Finset.range (J + 1)).biUnion (fun j => (Finset.univ : Finset C).powersetCard j) := by
    intro S hS
    have hj := (Finset.mem_filter.mp hS).2
    exact Finset.mem_biUnion.mpr ⟨S.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  calc
    _ ≤ ((Finset.range (J + 1)).biUnion (fun j => (Finset.univ : Finset C).powersetCard j)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (J + 1), ((Finset.univ : Finset C).powersetCard j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (J + 1), Fintype.card C ^ J := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hC (by have := Finset.mem_range.mp hj; omega))
    _ = _ := by simp

end Erdos911
