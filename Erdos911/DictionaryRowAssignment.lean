import Erdos911.DictionaryEventWeights

open MeasureTheory

namespace Erdos911

/-- One assignment of coordinates to all low host rows avoids every
connected-support, dyadic-scale and small-coordinate-subset bad event. -/
theorem exists_dictionary_row_assignment {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (hq : 2 ^ 32 ≤ q) :
    ∃ f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q),
      ∀ W ∈ smallConnectedSets (concreteDictionaryGraph K q) (dictionaryLeftSize q),
        ∀ j, AdmissibleDictionaryScale K q W j →
          ∀ S : Finset (Fin (dictionaryWordLength q)), S.card ≤ dictionaryBadLimit q →
            (eventHitSet (fun y => labelSubsetEvent y S) (dictionaryRowSupport K q W) f).card <
              dictionaryRowThreshold q (2 ^ j) := by
  classical
  let Y := ↥(dictionaryLowVertices K (dictionaryLowDegree q))
  let C := Fin (dictionaryWordLength q)
  let A := dictionaryCoordinateBadEvent K q
  let D := dictionaryCoordinateEventRows K q
  let w := fun e : DictionaryCoordinateEvent K q =>
    dictionaryRowEventWeight q (dictionaryCoordinateEventSize K q e)
  have hnonneg (e : DictionaryCoordinateEvent K q) : 0 ≤ w e := (Real.exp_pos _).le
  have hhalf (e : DictionaryCoordinateEvent K q) : w e ≤ 1 / 2 :=
    dictionaryRowEventWeight_half q _ hq (dictionaryCoordinateEvent_scale_lower K q e)
  obtain ⟨hpos, _⟩ := coordinate_lll_from_exp_bounds_fintype
    (fun _ : Y => (PMF.uniformOfFintype C).toMeasure) A D
    (dictionaryCoordinateBadEvent_depends K q) w (dictionaryRowWeightBudget q)
    hnonneg hhalf (dictionary_coordinate_event_budget K q hq)
    (dictionary_event_lll_probability K q hq)
  have hne : (avoidAll A).Nonempty := by
    by_contra hn
    have he : avoidAll A = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he, measureReal_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨f, hf⟩ := hne
  refine ⟨f, ?_⟩
  intro W hW j hj S hS
  have hWpos : W.Nonempty := Finset.card_pos.mp ((mem_smallConnectedSets _ _ _).mp hW).1
  let e : DictionaryCoordinateEvent K q := ⟨⟨W, hW⟩,
    ⟨⟨j, (mem_dictionaryScales K q W hWpos j).mpr hj⟩,
      ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩⟩⟩
  exact Nat.lt_of_not_ge (hf e)

end Erdos911
