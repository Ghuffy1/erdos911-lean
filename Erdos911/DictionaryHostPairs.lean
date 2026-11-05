import Erdos911.ConcreteDictionaryLabels

namespace Erdos911

/-- Distinct common rows provide a lower bound on incidence codegree. -/
theorem incidenceCodegree_ge_shared_rows {V R Y : Type*}
    [DecidableEq V] [DecidableEq R] [Fintype Y]
    (N : Y → Finset V) (x z : V) (T : Finset R) (r : R → Y)
    (hr : Function.Injective r) (hrows : ∀ y ∈ T, x ∈ N (r y) ∧ z ∈ N (r y)) :
    T.card ≤ incidenceCodegree N x z := by
  classical
  have hsub : T.image r ⊆ incidenceColumn N x ∩ incidenceColumn N z := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hrows t ht).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hrows t ht).2⟩⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hr] at h
  simpa only [incidenceCodegree] using h

/-- A sufficiently repeated low-row pattern forms an edge in the
relative host conflict graph, provided the image degrees are bounded. -/
theorem dictionaryHostGraph_adj_of_shared_rows {V R : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq R]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (C H : ℝ) (hC : 0 ≤ C)
    (x z : V) (hne : x ≠ z) (hx : D < K.degree x) (hz : D < K.degree z)
    (hxH : (K.degree x : ℝ) ≤ H) (hzH : (K.degree z : ℝ) ≤ H)
    (T : Finset R) (r : R → ↥(dictionaryLowVertices K D)) (hr : Function.Injective r)
    (hrows : ∀ y ∈ T, K.Adj x (r y).val ∧ K.Adj z (r y).val)
    (hscale : H ≤ C * T.card) :
    (dictionaryHostGraph K D C).Adj x z := by
  classical
  have hcommon : T.card ≤ incidenceCodegree (dictionaryHostRows K D) x z := by
    apply incidenceCodegree_ge_shared_rows (dictionaryHostRows K D) x z T r hr
    intro y hy
    exact ⟨(mem_restrictedHostRows K _ _ (r y) x).mpr ⟨Finset.mem_univ _, (hrows y hy).1⟩,
      (mem_restrictedHostRows K _ _ (r y) z).mpr ⟨Finset.mem_univ _, (hrows y hy).2⟩⟩
  have hcommonR : (T.card : ℝ) ≤ incidenceCodegree (dictionaryHostRows K D) x z := by exact_mod_cast hcommon
  refine ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, ?_⟩
  exact (max_le hxH hzH).trans (hscale.trans (mul_le_mul_of_nonneg_left hcommonR hC))

end Erdos911
