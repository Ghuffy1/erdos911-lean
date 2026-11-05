import Erdos911.NeighborhoodCenterSelection
import Erdos911.ListCoveringRounds

namespace Erdos911

theorem mem_commonCenters_iff {X W : Type*} [Fintype W]
    (R : X → W → Prop) (Y : Finset X) (z : W) :
    z ∈ commonCenters R Y ↔ ∀ x ∈ Y, R x z := by
  classical
  simp only [commonCenters, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Tuples whose intersection exceeds the permitted size have empty support. -/
noncomputable def boundedNeighborhoodTupleBlock {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) (q : ℕ) {t : ℕ} (z : Fin t → W) : Finset W := by
  classical
  exact if (neighborhoodTupleBlock H X z).card ≤ q then neighborhoodTupleBlock H X z else ∅

theorem boundedNeighborhoodTupleBlock_of_card_le {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) (q : ℕ) {t : ℕ} (z : Fin t → W)
    (hz : (neighborhoodTupleBlock H X z).card ≤ q) :
    boundedNeighborhoodTupleBlock H X q z = neighborhoodTupleBlock H X z := by
  classical
  simp only [boundedNeighborhoodTupleBlock, ite_eq_left hz]

theorem boundedNeighborhoodTupleBlock_subset {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) (q : ℕ) {t : ℕ} (z : Fin t → W) :
    boundedNeighborhoodTupleBlock H X q z ⊆ neighborhoodTupleBlock H X z := by
  classical
  unfold boundedNeighborhoodTupleBlock
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.empty_subset _

theorem boundedNeighborhoodTupleBlock_card_le {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) (q : ℕ) {t : ℕ} (z : Fin t → W) :
    (boundedNeighborhoodTupleBlock H X q z).card ≤ q := by
  classical
  unfold boundedNeighborhoodTupleBlock
  split_ifs with hz
  · exact hz
  · simp only [Finset.card_empty, Nat.zero_le]

theorem boundedNeighborhoodTupleBlock_family_size {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X : Finset W) (q t D : ℕ)
    (hD : ∀ x ∈ X, H.degree x ≤ D) (A : Finset (Fin t → W)) :
    (∑ z ∈ A, (boundedNeighborhoodTupleBlock H X q z).card) ≤ X.card * D ^ t := by
  apply (Finset.sum_le_sum (fun z _ => Finset.card_le_card
    (boundedNeighborhoodTupleBlock_subset H X q z))).trans
  exact neighborhoodTupleBlock_family_size H X t D hD A

theorem tuple_progress_from_centers {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X U Y : Finset W) (t D q : ℕ) (T R δ : ℝ)
    [DecidableRel (highCodegreeGraph H R).Adj]
    (ht : 0 < t) (x : W) (hx : x ∈ X) (hYX : Y ⊆ X)
    (hU : ∀ u ∈ U, H.Adj x u) (hD : ∀ w, H.degree w ≤ D) (hT : 0 < T) (hR : 0 ≤ R)
    (hUsize : T / 4 ≤ (U.card : ℝ)) (hQ : (highCodegreeGraph H R).degree x < q)
    (hgap : (D : ℝ) ^ 2 * R ^ t ≤ (T / 4) ^ t / 2)
    (hmiss : ∀ u ∈ U, ((Y.filter (fun y => ¬H.Adj y u)).card : ℝ) ≤ δ * Y.card) :
    ∃ A : Finset (Fin t → W), (T / 4) ^ t / 2 ≤ (A.card : ℝ) ∧
      ∀ z ∈ A, ((Y \ boundedNeighborhoodTupleBlock H X q z).card : ℝ) ≤ t * δ * Y.card := by
  classical
  have hpower : (T / 4) ^ t ≤ (U.card : ℝ) ^ t := pow_le_pow_left₀ (by positivity) hUsize t
  have hgapU : (D : ℝ) ^ 2 * R ^ t ≤ (U.card : ℝ) ^ t / 2 := hgap.trans (by linarith)
  obtain ⟨hcount, hblocks⟩ := highCodegreeTuple_supply H X U Y t D q R δ ht x hx hYX hU hD hR hQ hgapU hmiss
  let A := confinedNeighborhoodTuples H X U (insert x (neighbors (highCodegreeGraph H R) x)) t
  refine ⟨A, by dsimp only [A]; linarith, ?_⟩
  intro z hz
  obtain ⟨_, hsize, hcoverage⟩ := hblocks z hz
  rw [boundedNeighborhoodTupleBlock_of_card_le H X q z hsize]
  have hpartition : ((Y \ neighborhoodTupleBlock H X z).card : ℝ) +
      ((Y ∩ neighborhoodTupleBlock H X z).card : ℝ) = Y.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Y (neighborhoodTupleBlock H X z)
  nlinarith only [hpartition, hcoverage]

/-- The same family of bounded neighborhood intersections supports full
coverage of small lists and contraction of arbitrary residual sublists. -/
theorem neighborhoodTuple_progress_families {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X Z : Finset W) (s t D q : ℕ) (D₀ T R θ : ℝ)
    [DecidableRel (highCodegreeGraph H R).Adj]
    (hs : 2 ≤ s) (ht : 0 < t) (hZX : Z ⊆ X) (hD₀ : 0 < D₀) (hT : 0 < T) (hR : 0 ≤ R)
    (hD : ∀ w, H.degree w ≤ D)
    (hsingle : ∀ x ∈ Z, ((commonCenters H.Adj {x}).card : ℝ) ≤ D₀)
    (hcommon : ∀ Y ⊆ Z, Y.card ≤ s → T ≤ ((commonCenters H.Adj Y).card : ℝ))
    (hQ : ∀ x ∈ X, (highCodegreeGraph H R).degree x < q)
    (hgap : (D : ℝ) ^ 2 * R ^ t ≤ (T / 4) ^ t / 2)
    (hθ : Real.log (2 * D₀ / T) / ((s - 1 : ℕ) : ℝ) ≤ θ) (hθhalf : θ ≤ 1 / 2) :
    (∀ Y ⊆ Z, Y.Nonempty → (Y.card : ℝ) ≤ s →
      ∃ A : Finset (Fin t → W), (T / 4) ^ t / 2 ≤ (A.card : ℝ) ∧
        ∀ z ∈ A, Y ⊆ boundedNeighborhoodTupleBlock H X q z) ∧
    (∀ Y ⊆ Z, Y.Nonempty →
      ∃ A : Finset (Fin t → W), (T / 4) ^ t / 2 ≤ (A.card : ℝ) ∧
        ∀ z ∈ A, ((Y \ boundedNeighborhoodTupleBlock H X q z).card : ℝ) ≤ (t : ℝ) * θ * Y.card) := by
  classical
  constructor
  · intro Y hYZ hY hYsize
    obtain ⟨x, hx⟩ := hY
    let U := commonCenters H.Adj Y
    have hUsize : T / 4 ≤ (U.card : ℝ) := by
      have h := hcommon Y hYZ (by exact_mod_cast hYsize)
      linarith
    have hU : ∀ u ∈ U, H.Adj x u := by
      intro u hu
      exact (mem_commonCenters_iff H.Adj Y u).mp hu x hx
    have hmiss : ∀ u ∈ U, ((Y.filter (fun y => ¬H.Adj y u)).card : ℝ) ≤ (0 : ℝ) * Y.card := by
      intro u hu
      have heq : Y.filter (fun y => ¬H.Adj y u) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨hyY, hyNot⟩ := Finset.mem_filter.mp hy
        exact hyNot ((mem_commonCenters_iff H.Adj Y u).mp hu y hyY)
      simp only [heq, Finset.card_empty, Nat.cast_zero, zero_mul, le_refl]
    obtain ⟨A, hA, hdecrease⟩ := tuple_progress_from_centers H X U Y t D q T R 0 ht x
      (hZX (hYZ hx)) (hYZ.trans hZX) hU hD hT hR hUsize (hQ x (hZX (hYZ hx))) hgap hmiss
    refine ⟨A, hA, ?_⟩
    intro z hz
    apply Finset.sdiff_eq_empty_iff_subset.mp
    apply Finset.card_eq_zero.mp
    have hzero : ((Y \ boundedNeighborhoodTupleBlock H X q z).card : ℝ) ≤ 0 := by
      simpa only [mul_zero, zero_mul] using hdecrease z hz
    have hnat : (Y \ boundedNeighborhoodTupleBlock H X q z).card ≤ 0 := by exact_mod_cast hzero
    omega
  · intro Y hYZ hY
    obtain ⟨x, hx, U, hUsize, hU, hrows⟩ := select_candidate_centers H Y s D₀ T hs hY hD₀ hT
      (fun x hx => hsingle x (hYZ hx)) (fun Q hQ hsize => hcommon Q (hQ.trans hYZ) hsize)
      (hθ.trans hθhalf)
    have hmiss : ∀ u ∈ U, ((Y.filter (fun y => ¬H.Adj y u)).card : ℝ) ≤ θ * Y.card := by
      intro u hu
      have hpartition : ((Y.filter (fun y => H.Adj y u)).card : ℝ) +
          ((Y.filter (fun y => ¬H.Adj y u)).card : ℝ) = Y.card := by
        exact_mod_cast Finset.card_filter_add_card_filter_not (s := Y) (p := fun y => H.Adj y u)
      have hscaled := mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg (α := ℝ) Y.card)
      nlinarith only [hpartition, hrows u hu, hscaled]
    exact tuple_progress_from_centers H X U Y t D q T R θ ht x
      (hZX (hYZ hx)) (hYZ.trans hZX) hU hD hT hR hUsize (hQ x (hZX (hYZ hx))) hgap hmiss

/-- Independent rounds of bounded intersection marks cover a complete
candidate list with a uniform, explicit probability lower bound. -/
theorem neighborhood_tuple_cover_probability {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X Z : Finset W) (s t D q h : ℕ)
    (D₀ T R θ p β : ℝ) [DecidableRel (highCodegreeGraph H R).Adj]
    (hs : 2 ≤ s) (ht : 0 < t) (hZX : Z ⊆ X) (hD₀ : 0 < D₀) (hT : 0 < T) (hR : 0 ≤ R)
    (hD : ∀ w, H.degree w ≤ D)
    (hsingle : ∀ x ∈ Z, ((commonCenters H.Adj {x}).card : ℝ) ≤ D₀)
    (hcommon : ∀ Y ⊆ Z, Y.card ≤ s → T ≤ ((commonCenters H.Adj Y).card : ℝ))
    (hQ : ∀ x ∈ X, (highCodegreeGraph H R).degree x < q)
    (hgap : (D : ℝ) ^ 2 * R ^ t ≤ (T / 4) ^ t / 2)
    (hθ : Real.log (2 * D₀ / T) / ((s - 1 : ℕ) : ℝ) ≤ θ)
    (hθ₀ : 0 ≤ θ) (hθhalf : θ ≤ 1 / 2)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hβ : 0 ≤ β)
    (hβbound : β ≤ 1 - Real.exp (-p * ((T / 4) ^ t / 2)))
    (hinitial : ((t : ℝ) * θ) ^ h * (Z.card : ℝ) ≤ s) :
    β ^ (h + 1) ≤
      (MeasureTheory.Measure.pi (fun _ : Fin (h + 1) => bitProductMeasure (Fin t → W) p hp₀ hp₁)).real
        {marks | runRounds (uncoveredVertices (boundedNeighborhoodTupleBlock H X q)) Z marks = ∅} := by
  obtain ⟨hsmall, hshrink⟩ := neighborhoodTuple_progress_families H X Z s t D q D₀ T R θ
    hs ht hZX hD₀ hT hR hD hsingle hcommon hQ hgap hθ hθhalf
  exact independent_list_cover_probability (boundedNeighborhoodTupleBlock H X q) Z s h
    ((t : ℝ) * θ) p ((T / 4) ^ t / 2) β (mul_nonneg (Nat.cast_nonneg _) hθ₀)
    hp₀ hp₁ hβ hβbound hsmall hshrink hinitial

end Erdos911
