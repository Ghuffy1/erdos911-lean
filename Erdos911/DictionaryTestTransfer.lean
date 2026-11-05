import Erdos911.TargetBlockTests

namespace Erdos911

theorem dictionaryBadCoordinate_congr_on {L C R : Type*} [Fintype C]
    (N N' : R → Finset L) (U : Finset R) (hrow : ∀ y ∈ U, N y = N' y) (j : C) :
    dictionaryBadCoordinate N U j = dictionaryBadCoordinate N' U j := by
  classical
  ext ω
  have hhit : eventHitSet (fun y => dictionaryUniformRow (N y) j) U ω =
      eventHitSet (fun y => dictionaryUniformRow (N' y) j) U ω := by
    ext y
    simp only [mem_eventHitSet]
    constructor
    · rintro ⟨hy, hh⟩
      exact ⟨hy, by simpa only [hrow y hy] using hh⟩
    · rintro ⟨hy, hh⟩
      exact ⟨hy, by simpa only [hrow y hy] using hh⟩
  change U.card < 4 * Fintype.card C * (eventHitSet (fun y => dictionaryUniformRow (N y) j) U ω).card ↔
    U.card < 4 * Fintype.card C * (eventHitSet (fun y => dictionaryUniformRow (N' y) j) U ω).card
  rw [hhit]

/-- A good target block controls every injective labeling of a selected
left subset, with exactly the right rows whose truncated patterns lie there. -/
theorem block_dictionary_controls_subset {A R : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    (N : R → Finset A) (q : ℕ)
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool)
    (hgood : BlockDictionaryGood N q ω) (U : Finset A)
    (c : A → Fin (dictionaryLabelCount q)) (hc : Set.InjOn c (U : Set A)) :
    let B := (substantialTargetRows (targetTruncatedRows N (dictionaryLowDegree q)) (dictionaryRowMinimum q)).filter
      (fun y => targetTruncatedRows N (dictionaryLowDegree q) y ⊆ U)
    (eventHitSet (dictionaryBadCoordinate
      (fun y => (targetTruncatedRows N (dictionaryLowDegree q) y).image c) B) Finset.univ ω).card <
        dictionaryBadLimit q := by
  classical
  let f := restrictPartialLabel U c
  have hg := hgood f
  have hrows : blockTestRows N q f =
      (substantialTargetRows (targetTruncatedRows N (dictionaryLowDegree q)) (dictionaryRowMinimum q)).filter
        (fun y => targetTruncatedRows N (dictionaryLowDegree q) y ⊆ U) :=
    partialLabelTestRows_restrict _ _ U c hc
  rw [hrows] at hg
  let B := (substantialTargetRows (targetTruncatedRows N (dictionaryLowDegree q)) (dictionaryRowMinimum q)).filter
    (fun y => targetTruncatedRows N (dictionaryLowDegree q) y ⊆ U)
  have hneighborhood (y : R) (hy : y ∈ B) : blockTestNeighborhoods N q f y =
      (targetTruncatedRows N (dictionaryLowDegree q) y).image c :=
    partialLabelRange_restrict U _ c (Finset.mem_filter.mp hy).2
  have hevents : dictionaryBadCoordinate (C := Fin (dictionaryWordLength q)) (blockTestNeighborhoods N q f) B =
      dictionaryBadCoordinate (fun y => (targetTruncatedRows N (dictionaryLowDegree q) y).image c) B := by
    funext j
    exact dictionaryBadCoordinate_congr_on (C := Fin (dictionaryWordLength q)) _ _ B hneighborhood j
  rw [hevents] at hg
  exact hg

end Erdos911
