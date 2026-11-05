import Erdos911.SeedMatchingMarks

namespace Erdos911

theorem boundedNeighborhoodTupleBlock_incidence_le_on {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (X : Finset W) (q t D : ℕ)
    (hD : ∀ x ∈ X, J.degree x ≤ D) (x : W) :
    ((Finset.univ : Finset (Fin t → W)).filter
      (fun z => x ∈ boundedNeighborhoodTupleBlock J X q z)).card ≤ D ^ t := by
  classical
  let A := (Finset.univ : Finset (Fin t → W)).filter
    (fun z => x ∈ boundedNeighborhoodTupleBlock J X q z)
  have hsub : A ⊆ (Finset.univ : Finset (Fin t → W)).filter
      (fun z => x ∈ neighborhoodTupleBlock J X z) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      boundedNeighborhoodTupleBlock_subset J X q z (Finset.mem_filter.mp hz).2⟩
  by_cases hx : x ∈ X
  · exact (Finset.card_le_card hsub).trans (by
      rw [neighborhoodTupleBlock_incidence J X t x hx]
      exact Nat.pow_le_pow_left (hD x hx) t)
  · have hEmpty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hx (neighborhoodTupleBlock_subset J X z (Finset.mem_filter.mp (hsub hz)).2)
    change A.card ≤ D ^ t
    rw [hEmpty, Finset.card_empty]
    exact Nat.zero_le _

theorem boundedNeighborhoodTupleBlock_incidence_le {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (X : Finset W) (q t D : ℕ)
    (hD : ∀ x, J.degree x ≤ D) (x : W) :
    ((Finset.univ : Finset (Fin t → W)).filter
      (fun z => x ∈ boundedNeighborhoodTupleBlock J X q z)).card ≤ D ^ t :=
  boundedNeighborhoodTupleBlock_incidence_le_on J X q t D (fun x _ => hD x) x

theorem boundedNeighborhoodTupleBlock_round_size_on {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (X : Finset W) (q t D h : ℕ)
    (hD : ∀ x ∈ X, J.degree x ≤ D) :
    (∑ e : Fin h × (Fin t → W), ((boundedNeighborhoodTupleBlock J X q e.2).card : ℝ)) ≤
      (h : ℝ) * X.card * (D : ℝ) ^ t := by
  have hbound : (∑ z : Fin t → W, ((boundedNeighborhoodTupleBlock J X q z).card : ℝ)) ≤
      X.card * (D : ℝ) ^ t := by
    exact_mod_cast boundedNeighborhoodTupleBlock_family_size J X q t D hD Finset.univ
  calc
    _ = (h : ℝ) * ∑ z : Fin t → W, ((boundedNeighborhoodTupleBlock J X q z).card : ℝ) := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ ≤ (h : ℝ) * (X.card * (D : ℝ) ^ t) := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg h)
    _ = _ := by ring

theorem boundedNeighborhoodTupleBlock_round_size {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (X : Finset W) (q t D h : ℕ)
    (hD : ∀ x, J.degree x ≤ D) :
    (∑ e : Fin h × (Fin t → W), ((boundedNeighborhoodTupleBlock J X q e.2).card : ℝ)) ≤
      (h : ℝ) * X.card * (D : ℝ) ^ t :=
  boundedNeighborhoodTupleBlock_round_size_on J X q t D h (fun x _ => hD x)

/-- Geometric list blocking, canonical matching, seed incidence, and
conditional cost control use one shared family of tuple marks. -/
theorem exists_neighborhood_seed_marks {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hhost : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D)
    (s r t q₁ q₂ h m : ℕ) (τ D₀ T R θ p β u a ν : ℝ) (hτ : 0 < τ)
    (C : Finset (SeedDescription F H s)) (X : Finset W)
    [DecidableRel (highCodegreeGraph J R).Adj]
    (hr : 2 ≤ r) (ht : 0 < t) (hq₂ : 0 < q₂)
    (hsize : ∀ c : C, ∀ v, (unseededCandidateList F H J s τ c.val v).card ≤ q₁)
    (hLX : ∀ c : C, ∀ v : thickCandidateRoles J (unseededCandidateList F H J s τ c.val) r T,
      unseededCandidateList F H J s τ c.val v.val ⊆ X)
    (hD₀ : 0 < D₀) (hT : 0 < T) (hR : 0 ≤ R) (hRT : R < T)
    (hsingle : ∀ x ∈ X, ((commonCenters J.Adj {x}).card : ℝ) ≤ D₀)
    (hQ : ∀ x ∈ X, (highCodegreeGraph J R).degree x < q₂)
    (hgap : (D : ℝ) ^ 2 * R ^ t ≤ (T / 4) ^ t / 2)
    (hθ : Real.log (2 * D₀ / T) / ((r - 1 : ℕ) : ℝ) ≤ θ)
    (hθ₀ : 0 ≤ θ) (hθhalf : θ ≤ 1 / 2)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hβ : 0 ≤ β)
    (hβbound : β ≤ 1 - Real.exp (-p * ((T / 4) ^ t / 2)))
    (hinitial : ∀ c : C, ∀ v : thickCandidateRoles J (unseededCandidateList F H J s τ c.val) r T,
      ((t : ℝ) * θ) ^ h * ((unseededCandidateList F H J s τ c.val v.val).card : ℝ) ≤ r)
    (hmass : ∀ c : C, m ≤ (matchedRoles (maximumListMatching (fun v :
      thickCandidateRoles J (unseededCandidateList F H J s τ c.val) r T =>
        unseededCandidateList F H J s τ c.val v.val))).card)
    (hu : u ≤ β ^ (h + 1) * m / 2)
    (ha : a ≤ β ^ (h + 1) * m / (8 * (q₂ * q₂ : ℕ)))
    (hν : 0 ≤ ν) (hhalf : Real.exp (-a / 2) ≤ 1 / 2)
    (hincidence : (q₂ * (Fintype.card V * (D + 1) *
      ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)) : ℝ) * Real.exp (-a / 2) ≤ ν)
    (hsizegap : 4 * ν * ((h + 1) * Fintype.card V * q₁ * D ^ t : ℕ) ≤ a)
    (hfactor : Real.exp (2 * ν) ≤ 2) :
    ∃ marks : (Fin (h + 1) × (Fin t → W)) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T
        (boundedNeighborhoodTupleBlock J X q₂) (h + 1) u) ∧
      (∑ e, if marks e = true then ((boundedNeighborhoodTupleBlock J X q₂ e.2).card : ℝ) else 0) ≤
        (2 * p) * (h + 1) * X.card * (D : ℝ) ^ t := by
  classical
  have hD : ∀ w, J.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE J H hJ).degree_le w).trans (hhost w)
  let B : (Fin t → W) → Finset W := boundedNeighborhoodTupleBlock J X q₂
  have hprob (c : C) : (bitProductMeasure (Fin (h + 1) × (Fin t → W)) p hp₀ hp₁).real
      (thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B (h + 1) u) ≤ Real.exp (-a) := by
    apply (thickMatchingEvent_probability J X (unseededCandidateList F H J s τ c.val)
      r t D q₂ h m D₀ T R θ p β u hr ht hq₂ (hLX c) hD₀ hT hR hRT hD hsingle hQ
      hgap hθ hθ₀ hθhalf hp₀ hp₁ hβ hβbound (hinitial c) (hmass c) hu).trans
    exact Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg ha)
  obtain ⟨marks, hmarks, hcost⟩ := exists_seed_matching_marks F H J hJ Δ D hΔ hhost hΔpos hDpos
    s r τ T hτ C B (h + 1) q₁ q₂ (D ^ t)
    (fun z => boundedNeighborhoodTupleBlock_card_le J X q₂ z) hsize
    (fun _ _ w _ => boundedNeighborhoodTupleBlock_incidence_le J X q₂ t D hD w)
    p a ν u hp₀ hp₁ hν hprob hhalf hincidence hsizegap hfactor
    (fun e => ((B e.2).card : ℝ)) (fun _ => Nat.cast_nonneg _)
  refine ⟨marks, hmarks, hcost.trans ?_⟩
  calc
    _ ≤ (2 * p) * ((h + 1) * X.card * (D : ℝ) ^ t) :=
      mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using
        boundedNeighborhoodTupleBlock_round_size J X q₂ t D (h + 1) hD)
        (by positivity)
    _ = _ := by ring

end Erdos911
