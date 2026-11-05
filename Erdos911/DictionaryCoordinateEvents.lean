import Erdos911.DictionaryRowSupport
import Erdos911.SmallCoordinateSets
import Erdos911.RowCoordinateParameters
import Erdos911.UniformSubsetTails

namespace Erdos911

noncomputable abbrev DictionaryCoordinateEvent {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) :=
  Σ W : ↥(smallConnectedSets (concreteDictionaryGraph K q) (dictionaryLeftSize q)),
    ↥(dictionaryScales K q W.val) × ↥(smallCoordinateSets (Fin (dictionaryWordLength q)) (dictionaryBadLimit q))

noncomputable def dictionaryCoordinateEventRows {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (e : DictionaryCoordinateEvent K q) :=
  dictionaryRowSupport K q e.1.val

def dictionaryCoordinateEventSize {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (e : DictionaryCoordinateEvent K q) : ℕ := 2 ^ e.2.1.val

def dictionaryCoordinateBadEvent {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (e : DictionaryCoordinateEvent K q) :
    Set (↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q)) :=
  {f | dictionaryRowThreshold q (dictionaryCoordinateEventSize K q e) ≤
    (eventHitSet (fun y => labelSubsetEvent y e.2.2.val) (dictionaryCoordinateEventRows K q e) f).card}

theorem dictionaryCoordinateBadEvent_depends {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (e : DictionaryCoordinateEvent K q) :
    DependsOnlyOn (dictionaryCoordinateBadEvent K q e) (dictionaryCoordinateEventRows K q e) := by
  intro f g heq hf
  have hA (y) (hy : y ∈ dictionaryCoordinateEventRows K q e) :
      DependsOnlyOn (labelSubsetEvent y e.2.2.val) (dictionaryCoordinateEventRows K q e) :=
    (labelSubsetEvent_depends y e.2.2.val).mono (Finset.singleton_subset_iff.mpr hy)
  have hh := eventHitSet_eq_of_agreement (fun y => labelSubsetEvent y e.2.2.val)
    (dictionaryCoordinateEventRows K q e) _ hA f g heq
  change dictionaryRowThreshold q (dictionaryCoordinateEventSize K q e) ≤
    (eventHitSet (fun y => labelSubsetEvent y e.2.2.val) (dictionaryCoordinateEventRows K q e) g).card
  rw [← hh]
  exact hf

theorem dictionaryCoordinateEventRows_card {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (e : DictionaryCoordinateEvent K q) :
    (dictionaryCoordinateEventRows K q e).card ≤
      2 * dictionaryLeftSize q * dictionaryDegreeCharge q * dictionaryCoordinateEventSize K q e := by
  classical
  have hW := (mem_smallConnectedSets _ _ _).mp e.1.property
  exact dictionaryRowSupport_card_le K q e.1.val e.2.1.val hW.2.1 (Finset.mem_filter.mp e.2.1.property).2

theorem dictionaryCoordinateEvent_scale_lower {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (e : DictionaryCoordinateEvent K q) :
    8 * dictionaryLeftSize q * dictionaryLowDegree q ≤ q * dictionaryCoordinateEventSize K q e := by
  classical
  exact ((Finset.mem_filter.mp e.2.1.property).2).1

end Erdos911
