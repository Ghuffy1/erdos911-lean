import Erdos911.RelativeCodegreeGraph
import Erdos911.PairHostColoring

namespace Erdos911

noncomputable def dictionaryLowVertices {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => K.degree v ≤ D)

noncomputable def dictionaryHighVertices {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => D < K.degree v)

noncomputable def dictionaryHostRows {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) : ↥(dictionaryLowVertices K D) → Finset V :=
  restrictedHostRows K Finset.univ (dictionaryLowVertices K D)

noncomputable def dictionaryHostGraph {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (C : ℝ) : SimpleGraph V :=
  relativeCodegreeGraph (dictionaryHostRows K D) (dictionaryHighVertices K D)
    (fun x => K.degree x) C

theorem dictionaryHostRows_row_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (y : ↥(dictionaryLowVertices K D)) :
    (dictionaryHostRows K D y).card ≤ D :=
  (restrictedHostRows_row_bound K _ _ y).trans (Finset.mem_filter.mp y.property).2

theorem dictionaryHostRows_column_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (x : V) :
    (incidenceColumn (dictionaryHostRows K D) x).card ≤ K.degree x := by
  classical
  let N := dictionaryHostRows K D
  have hsub : (incidenceColumn N x).image Subtype.val ⊆ K.neighborFinset x := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hm := (Finset.mem_filter.mp hz).2
    exact (K.mem_neighborFinset x z.val).mpr ((mem_restrictedHostRows K _ _ z x).mp hm).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective, K.card_neighborFinset_eq_degree] at hc
  exact hc

/-- The conflict graph used by the dictionary has bounded degree even
when the original host has vertices of arbitrarily large degree. -/
theorem dictionaryHostGraph_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (C : ℝ) (hC : 0 ≤ C) (x : V) :
    letI : DecidableRel (dictionaryHostGraph K D C).Adj := Classical.decRel _
    ((dictionaryHostGraph K D C).degree x : ℝ) ≤ C * D := by
  classical
  apply relativeCodegreeGraph_degree_le (dictionaryHostRows K D) (dictionaryHighVertices K D)
    (fun v => K.degree v) C D hC (dictionaryHostRows_row_le K D)
  · intro v _
    exact_mod_cast dictionaryHostRows_column_le K D v
  · intro v hv
    have hh := (Finset.mem_filter.mp hv).2
    exact_mod_cast (show 0 < K.degree v by omega)

theorem dictionaryHostGraph_degree_le_ceil {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (C : ℝ) (hC : 0 ≤ C) (x : V) :
    letI : DecidableRel (dictionaryHostGraph K D C).Adj := Classical.decRel _
    (dictionaryHostGraph K D C).degree x ≤ Nat.ceil (C * D) := by
  have h := (dictionaryHostGraph_degree_le K D C hC x).trans (Nat.le_ceil (C * D))
  exact_mod_cast h

end Erdos911
