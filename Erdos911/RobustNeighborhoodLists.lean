import Erdos911.NeighborhoodTupleMarking
import Erdos911.BlockedListEvents

namespace Erdos911

theorem common_neighborhood_list_clique {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (Z : Finset W) (s : ℕ) (T R : ℝ) (hs : 2 ≤ s) (hRT : R < T)
    (hcommon : ∀ Y ⊆ Z, Y.card ≤ s → T ≤ ((commonCenters H.Adj Y).card : ℝ)) :
    ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → (highCodegreeGraph H R).Adj x y := by
  classical
  intro x hx y hy hxy
  have hsub : ({x, y} : Finset W) ⊆ Z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · have hzy : z = y := Finset.mem_singleton.mp hz
      exact hzy.symm ▸ hy
  have hcard : ({x, y} : Finset W).card ≤ s := by
    have hle : ({x, y} : Finset W).card ≤ 2 := by
      simpa only [Finset.card_singleton] using Finset.card_insert_le x ({y} : Finset W)
    omega
  have h := hcommon {x, y} hsub hcard
  have heq : commonCenters H.Adj {x, y} = neighbors H x ∩ neighbors H y := by
    ext z
    simp only [mem_commonCenters_iff, Finset.mem_insert, Finset.mem_singleton,
      forall_eq_or_imp, forall_eq, neighbors, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [heq] at h
  exact (highCodegreeGraph_adj H R x y).mpr ⟨hxy, hRT.trans_le h⟩

/-- A shared family of independent neighborhood-intersection marks
simultaneously gives the robust read-bound estimate for matched lists. -/
theorem robust_neighborhood_list_bound {J W : Type*} [Fintype J] [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X : Finset W) (L : J → Finset W)
    (s t D q h : ℕ) (D₀ T R θ p β u : ℝ)
    [DecidableRel (highCodegreeGraph H R).Adj]
    (hs : 2 ≤ s) (ht : 0 < t) (hq : 0 < q)
    (hLX : ∀ j, L j ⊆ X) (hD₀ : 0 < D₀) (hT : 0 < T) (hR : 0 ≤ R) (hRT : R < T)
    (hD : ∀ w, H.degree w ≤ D)
    (hsingle : ∀ x ∈ X, ((commonCenters H.Adj {x}).card : ℝ) ≤ D₀)
    (hcommon : ∀ j, ∀ Y ⊆ L j, Y.card ≤ s → T ≤ ((commonCenters H.Adj Y).card : ℝ))
    (hQ : ∀ x ∈ X, (highCodegreeGraph H R).degree x < q)
    (hgap : (D : ℝ) ^ 2 * R ^ t ≤ (T / 4) ^ t / 2)
    (hθ : Real.log (2 * D₀ / T) / ((s - 1 : ℕ) : ℝ) ≤ θ)
    (hθ₀ : 0 ≤ θ) (hθhalf : θ ≤ 1 / 2)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hβ : 0 ≤ β)
    (hβbound : β ≤ 1 - Real.exp (-p * ((T / 4) ^ t / 2)))
    (hinitial : ∀ j, ((t : ℝ) * θ) ^ h * ((L j).card : ℝ) ≤ s)
    (f : J → W) (hf : Function.Injective f) (hmem : ∀ j, f j ∈ L j)
    (hu : u ≤ β ^ (h + 1) * Fintype.card J / 2) :
    (bitProductMeasure (Fin (h + 1) × (Fin t → W)) p hp₀ hp₁).real
      {marks | (∑ j, (listBlocked (boundedNeighborhoodTupleBlock H X q) (h + 1) (L j)).indicator
        (fun _ => (1 : ℝ)) marks) ≤ u} ≤
      Real.exp (-(β ^ (h + 1) * Fintype.card J) / (8 * (q * q : ℕ))) := by
  classical
  let B : (Fin t → W) → Finset W := boundedNeighborhoodTupleBlock H X q
  have hclique : ∀ j, ∀ x ∈ L j, ∀ y ∈ L j, x ≠ y → (highCodegreeGraph H R).Adj x y :=
    fun j => common_neighborhood_list_clique H (L j) s T R hs hRT (hcommon j)
  have hprob : ∀ j, β ^ (h + 1) ≤
      (bitProductMeasure (Fin (h + 1) × (Fin t → W)) p hp₀ hp₁).real (listBlocked B (h + 1) (L j)) := by
    intro j
    rw [listBlocked_round_probability]
    exact neighborhood_tuple_cover_probability H X (L j) s t D q h D₀ T R θ p β
      hs ht (hLX j) hD₀ hT hR hD (fun x hx => hsingle x (hLX j hx)) (hcommon j)
      hQ hgap hθ hθ₀ hθhalf hp₀ hp₁ hβ hβbound (hinitial j)
  have hdegree : ∀ z x, x ∈ B z → (highCodegreeGraph H R).degree x < q := by
    intro z x hx
    apply hQ x
    exact neighborhoodTupleBlock_subset H X z (boundedNeighborhoodTupleBlock_subset H X q z hx)
  exact matched_lists_few_blocked (highCodegreeGraph H R) L f hf hmem hclique q hq B
    (fun z => boundedNeighborhoodTupleBlock_card_le H X q z) hdegree (h + 1)
    p (β ^ (h + 1)) u hp₀ hp₁ hprob hu

end Erdos911
