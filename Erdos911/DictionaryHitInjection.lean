import Erdos911.DictionaryRowSupport
import Erdos911.UniformSubsetTails

namespace Erdos911

theorem injective_rows_le_dictionary_hits {R V C : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V)
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → C) (S : Finset C)
    (T : Finset R) (g : R → V) (hinj : Set.InjOn g (T : Set R))
    (hlow : ∀ y ∈ T, K.degree (g y) ≤ dictionaryLowDegree q)
    (hsupport : ∀ y ∈ T, ∃ x ∈ W, K.Adj x (g y))
    (hcoord : ∀ y (hy : y ∈ T),
      f ⟨g y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow y hy⟩⟩ ∈ S) :
    T.card ≤ (eventHitSet (fun y => labelSubsetEvent y S) (dictionaryRowSupport K q W) f).card := by
  classical
  let E := eventHitSet (fun y => labelSubsetEvent y S) (dictionaryRowSupport K q W) f
  let m : ↥T → ↥E := fun y =>
    ⟨⟨g y.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow y.val y.property⟩⟩,
      (mem_eventHitSet _ _ _ _).mpr ⟨(mem_dictionaryRowSupport K q W _).mpr (hsupport y.val y.property),
        hcoord y.val y.property⟩⟩
  have hm : Function.Injective m := by
    intro y z heq
    apply Subtype.ext
    exact hinj y.property z.property (congrArg (fun t : ↥E => t.val.val) heq)
  have hh := Fintype.card_le_of_injective m hm
  simpa only [Fintype.card_coe] using hh

end Erdos911
