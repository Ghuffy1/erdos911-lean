import Erdos911.DictionaryBadCoordinates

namespace Erdos911

noncomputable def dictionaryGoodCoordinates {L C R : Type*} [Fintype C]
    (N : R → Finset L) (U : Finset R) (ω : (L × C) → Bool) : Finset C := by
  classical
  exact Finset.univ.filter (fun j => ω ∉ dictionaryBadCoordinate N U j)

noncomputable def dictionaryEverUniformGoodRows {L C R : Type*}
    [Fintype C] [DecidableEq R] (N : R → Finset L) (U : Finset R)
    (ω : (L × C) → Bool) : Finset R :=
  (dictionaryGoodCoordinates N U ω).biUnion
    (fun j => eventHitSet (fun y => dictionaryUniformRow (N y) j) U ω)

/-- At most one quarter of the rows are uniform in any good coordinate,
even after taking the union over all good coordinates. -/
theorem dictionary_good_coordinate_union {L C R : Type*}
    [Fintype C] [DecidableEq C] [DecidableEq R]
    (N : R → Finset L) (U : Finset R) (ω : (L × C) → Bool) :
    4 * (dictionaryEverUniformGoodRows N U ω).card ≤ U.card := by
  classical
  let G := dictionaryGoodCoordinates N U ω
  let rows := fun j => eventHitSet (fun y => dictionaryUniformRow (N y) j) U ω
  have hrow (j : C) (hj : j ∈ G) : 4 * Fintype.card C * (rows j).card ≤ U.card := by
    have hnot := (Finset.mem_filter.mp hj).2
    exact Nat.le_of_not_gt hnot
  have hsum := Finset.sum_le_sum (fun j hj => hrow j hj)
  have hsum' : 4 * Fintype.card C * (∑ j ∈ G, (rows j).card) ≤ G.card * U.card := by
    simpa only [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] using hsum
  have hcard : G.card * U.card ≤ Fintype.card C * U.card :=
    Nat.mul_le_mul_right _ (Finset.card_le_univ _)
  have hunion : (dictionaryEverUniformGoodRows N U ω).card ≤ ∑ j ∈ G, (rows j).card := Finset.card_biUnion_le
  by_cases hc : 0 < Fintype.card C
  · have hh := hsum'.trans hcard
    nlinarith only [hh, hunion, hc]
  · have hczero : Fintype.card C = 0 := by omega
    have hG : G = ∅ := Finset.card_eq_zero.mp (by have := Finset.card_le_univ G; omega)
    change 4 * (G.biUnion rows).card ≤ U.card
    rw [hG, Finset.biUnion_empty, Finset.card_empty, mul_zero]
    exact Nat.zero_le _

end Erdos911
