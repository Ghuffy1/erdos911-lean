import Erdos911.DictionaryCoordinateEvents
import Erdos911.FiniteFiberCounts

namespace Erdos911

/-- All scale and coordinate-subset events through one low row have a
uniform finite count, independent of the host's maximum degree. -/
theorem dictionaryCoordinateEvent_incidence_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (hq : 0 < q)
    (y : ↥(dictionaryLowVertices K (dictionaryLowDegree q))) :
    ((Finset.univ : Finset (DictionaryCoordinateEvent K q)).filter
      (fun e => y ∈ dictionaryCoordinateEventRows K q e)).card ≤ dictionaryRowEventCount q := by
  classical
  let W := ↥(smallConnectedSets (concreteDictionaryGraph K q) (dictionaryLeftSize q))
  let X := fun w : W => ↥(dictionaryScales K q w.val)
  let C := ↥(smallCoordinateSets (Fin (dictionaryWordLength q)) (dictionaryBadLimit q))
  let P := fun w : W => y ∈ dictionaryRowSupport K q w.val
  have hP : Fintype.card {w : W // P w} ≤ dictionaryLowDegree q *
      ((dictionaryLeftSize q + 1) * dictionaryConflictDegree q ^ (2 * dictionaryLeftSize q)) := by
    let F := (smallConnectedSets (concreteDictionaryGraph K q) (dictionaryLeftSize q)).filter
      (fun w => y ∈ dictionaryRowSupport K q w)
    let eF : {w : W // P w} ≃ ↥F :=
      { toFun := fun w => ⟨w.val.val, Finset.mem_filter.mpr ⟨w.val.property, w.property⟩⟩
        invFun := fun w => ⟨⟨w.val, (Finset.mem_filter.mp w.property).1⟩, (Finset.mem_filter.mp w.property).2⟩
        left_inv := fun w => by cases w; rfl
        right_inv := fun w => by cases w; rfl }
    have hc : Fintype.card {w : W // P w} = F.card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr eF
    rw [hc]
    exact dictionaryRowSupport_incidence_le K q hq y
  have hX (w : W) : Fintype.card (X w) ≤ 16 * dictionaryPatternCount q * dictionaryDegreeCharge q := by
    have hne : w.val.Nonempty := Finset.card_pos.mp ((mem_smallConnectedSets _ _ _).mp w.property).1
    simpa only [X, Fintype.card_coe] using dictionaryScales_card_le K q w.val hne
  have hC : Fintype.card C ≤ (dictionaryBadLimit q + 1) * dictionaryWordLength q ^ dictionaryBadLimit q := by
    have hw : 1 ≤ dictionaryWordLength q := by have := dictionaryWordLength_pos q; omega
    have hh := smallCoordinateSets_card_le (Fin (dictionaryWordLength q)) (dictionaryBadLimit q)
      (by simpa only [Fintype.card_fin] using hw)
    simpa only [C, Fintype.card_coe, Fintype.card_fin] using hh
  have hh := restricted_sigma_product_card_le X P _ _ _ hP hX hC
  let F := (Finset.univ : Finset (DictionaryCoordinateEvent K q)).filter
    (fun e => y ∈ dictionaryCoordinateEventRows K q e)
  let eF : ↥F ≃ {e : (Σ w : W, X w × C) // P e.1} :=
    { toFun := fun e => ⟨e.val, (Finset.mem_filter.mp e.property).2⟩
      invFun := fun e => ⟨e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property⟩⟩
      left_inv := fun e => by cases e; rfl
      right_inv := fun e => by cases e; rfl }
  have hc : F.card ≤ dictionaryLowDegree q *
      ((dictionaryLeftSize q + 1) * dictionaryConflictDegree q ^ (2 * dictionaryLeftSize q)) *
      ((16 * dictionaryPatternCount q * dictionaryDegreeCharge q) *
        ((dictionaryBadLimit q + 1) * dictionaryWordLength q ^ dictionaryBadLimit q)) := by
    have he := Fintype.card_congr eF
    rw [Fintype.card_coe] at he
    exact he.trans_le hh
  change F.card ≤ dictionaryRowEventCount q
  simpa only [dictionaryRowEventCount, Nat.mul_assoc] using hc

end Erdos911
