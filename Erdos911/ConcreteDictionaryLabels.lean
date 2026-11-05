import Erdos911.DictionaryParameters

namespace Erdos911

noncomputable abbrev concreteDictionaryGraph {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) : SimpleGraph V :=
  dictionaryHostGraph K (dictionaryLowDegree q)
    (16 * (dictionaryPatternCount q : ℝ) * dictionaryDegreeCharge q)

theorem concreteDictionaryGraph_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (v : V) :
    letI : DecidableRel (concreteDictionaryGraph K q).Adj := Classical.decRel _
    (concreteDictionaryGraph K q).degree v ≤ dictionaryConflictDegree q := by
  classical
  have hh := dictionaryHostGraph_degree_le K (dictionaryLowDegree q)
    (16 * (dictionaryPatternCount q : ℝ) * dictionaryDegreeCharge q) (by positivity) v
  have hbound : ((concreteDictionaryGraph K q).degree v : ℝ) ≤ (dictionaryConflictDegree q : ℝ) := by
    simpa only [dictionaryConflictDegree, Nat.cast_mul, Nat.cast_ofNat] using hh
  exact_mod_cast hbound

/-- Concrete labels used by the verified dictionary selection have
exactly the same cardinal bound as the labels needed by the host graph. -/
theorem exists_concrete_dictionary_labels {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) :
    ∃ c : V → Fin (dictionaryLabelCount q),
      ∀ S : Finset V, S.card ≤ dictionaryLeftSize q →
        ((concreteDictionaryGraph K q).induce (S : Set V)).Connected → Set.InjOn c (S : Set V) := by
  classical
  exact exists_connected_set_labels (concreteDictionaryGraph K q) (dictionaryConflictDegree q)
    (concreteDictionaryGraph_degree_le K q) (dictionaryLeftSize q)

end Erdos911
