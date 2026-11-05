import Erdos911.DictionaryGoodRows
import Erdos911.TargetPatternGraph

namespace Erdos911

noncomputable def assignedBadRows {L C R : Type*} [Fintype C] [DecidableEq R]
    (N : R → Finset L) (B U : Finset R) (τ : R → C) (ω : (L × C) → Bool) : Finset R := by
  classical
  exact (U ∩ B).filter (fun y => ω ∈ dictionaryBadCoordinate N B (τ y))

theorem assignedBadRows_cover {L C R : Type*}
    [Fintype C] [DecidableEq C] [DecidableEq R]
    (N : R → Finset L) (B U : Finset R) (τ : R → C) (ω : (L × C) → Bool)
    (huniform : ∀ y ∈ U, ω ∈ dictionaryUniformRow (N y) (τ y)) :
    (U ∩ B).card ≤ (dictionaryEverUniformGoodRows N B ω).card + (assignedBadRows N B U τ ω).card := by
  classical
  have hsub : U ∩ B ⊆ dictionaryEverUniformGoodRows N B ω ∪ assignedBadRows N B U τ ω := by
    intro y hy
    by_cases hb : ω ∈ dictionaryBadCoordinate N B (τ y)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hb⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨τ y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩,
        (mem_eventHitSet _ _ _ _).mpr ⟨(Finset.mem_inter.mp hy).2, huniform y (Finset.mem_inter.mp hy).1⟩⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem assignedBadRows_count {I L C R : Type*}
    [Fintype I] [Fintype C] [DecidableEq C] [DecidableEq R]
    (N : R → Finset L) (B : I → Finset R) (U : Finset R) (τ : R → C) (ω : (L × C) → Bool)
    (huniform : ∀ y ∈ U, ω ∈ dictionaryUniformRow (N y) (τ y))
    (hpartition : (∑ i, (U ∩ B i).card) = U.card)
    (b : ℕ) (hB : (∑ i, (B i).card) ≤ b) (hU : 3 * b ≤ 8 * U.card) :
    b ≤ 8 * (∑ i, (assignedBadRows N (B i) U τ ω).card) := by
  classical
  have hcover := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    assignedBadRows_cover N (B i) U τ ω huniform)
  rw [Finset.sum_add_distrib, hpartition] at hcover
  have hgood := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) =>
    dictionary_good_coordinate_union N (B i) ω)
  rw [← Finset.mul_sum] at hgood
  omega

theorem exists_large_assignedBadRows {I R : Type*} [Fintype I]
    (B : I → Finset R) (a b : ℕ) (hb : 0 < b) (hI : Fintype.card I ≤ a)
    (hsum : b ≤ 8 * (∑ i, (B i).card)) :
    ∃ i, b ≤ 8 * a * (B i).card := by
  classical
  have hne : Nonempty I := by
    by_contra hn
    have hi : IsEmpty I := not_nonempty_iff.mp hn
    let : IsEmpty I := hi
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero] at hsum
    omega
  obtain ⟨i₀⟩ := hne
  by_contra h
  push Not at h
  have hs := Finset.sum_lt_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => (h i).le)
    ⟨i₀, Finset.mem_univ _, h i₀⟩
  rw [← Finset.mul_sum] at hs
  have hcount : Fintype.card I * b ≤ a * b := Nat.mul_le_mul_right b hI
  have hs' : 8 * a * (∑ i, (B i).card) < Fintype.card I * b := by
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using hs
  have hm := Nat.mul_le_mul_left a hsum
  nlinarith only [hs', hcount, hm]

end Erdos911
