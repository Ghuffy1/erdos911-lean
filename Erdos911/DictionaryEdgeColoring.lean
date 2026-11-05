import Erdos911.DictionaryHostGraph
import Erdos911.DictionaryParameters

namespace Erdos911

noncomputable def dictionaryPairColor {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ)
    (c : V → Fin (dictionaryLabelCount q))
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool)
    (u v : V) : Bool :=
  if hu : K.degree u ≤ dictionaryLowDegree q then
    if dictionaryLowDegree q < K.degree v then ω (c v, f ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩)
    else false
  else
    if hv : K.degree v ≤ dictionaryLowDegree q then ω (c u, f ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)
    else false

theorem dictionaryPairColor_symm {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ)
    (c : V → Fin (dictionaryLabelCount q))
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool) (u v : V) :
    dictionaryPairColor K q c f ω u v = dictionaryPairColor K q c f ω v u := by
  by_cases hu : K.degree u ≤ dictionaryLowDegree q <;>
    by_cases hv : K.degree v ≤ dictionaryLowDegree q <;>
    simp [dictionaryPairColor, hu, hv, Nat.not_lt_of_ge, Nat.lt_of_not_ge]

noncomputable def dictionaryEdgeColor {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ)
    (c : V → Fin (dictionaryLabelCount q))
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨dictionaryPairColor K q c f ω, dictionaryPairColor_symm K q c f ω⟩

theorem dictionaryEdgeColor_high_low {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ)
    (c : V → Fin (dictionaryLabelCount q))
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool)
    (u v : V) (hu : dictionaryLowDegree q < K.degree u) (hv : K.degree v ≤ dictionaryLowDegree q) :
    dictionaryEdgeColor K q c f ω s(u, v) =
      ω (c u, f ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩) := by
  simp [dictionaryEdgeColor, dictionaryPairColor, Nat.not_le_of_lt hu, hv]

end Erdos911
