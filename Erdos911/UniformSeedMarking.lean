import Erdos911.SeedEventParameters
import Erdos911.TolerantSamplingParameters
import Erdos911.SeedMatchingMarks

namespace Erdos911

/-- The sampling choices discharge all local-lemma size and incidence
conditions uniformly in component order. The event probability bound
is supplied by the geometric matching estimate. -/
theorem uniform_tolerant_seed_marking (A h t : ℕ) (hh : 1 ≤ h) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W I : Type*)
    [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I],
    ∀ k D : ℕ, d ≤ k → d ≤ D → D ≤ d ^ A →
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj],
    J ≤ H → (∀ v, F.degree v ≤ D) → (∀ w, H.degree w ≤ D) →
    ∀ q₁ q₂ r : ℕ, 1 ≤ q₁ → 1 ≤ q₂ → q₁ ≤ d → q₂ ≤ d →
    ∀ (T p a u : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), seedEventExponent d k ≤ a →
    ∀ (C : Finset (SeedDescription F H (tolerantSamplingSeed A d k))) (B : I → Finset W),
    (∀ i, (B i).card ≤ q₂) →
    (∀ c : C, ∀ v, (unseededCandidateList F H J (tolerantSamplingSeed A d k)
      (1 - 4 * tolerantSamplingError d) c.val v).card ≤ q₁) →
    (∀ c : C, ∀ v w, w ∈ unseededCandidateList F H J (tolerantSamplingSeed A d k)
      (1 - 4 * tolerantSamplingError d) c.val v →
      (Finset.univ.filter (fun i => w ∈ B i)).card ≤ D ^ t) →
    (∀ c : C, (bitProductMeasure (Fin h × I) p hp₀ hp₁).real
      (thickMatchingEvent J (unseededCandidateList F H J (tolerantSamplingSeed A d k)
        (1 - 4 * tolerantSamplingError d) c.val) r T B h u) ≤ Real.exp (-a)) →
    ∀ cost : (Fin h × I) → ℝ, (∀ e, 0 ≤ cost e) →
    ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J (tolerantSamplingSeed A d k)
        (1 - 4 * tolerantSamplingError d) c.val) r T B h u) ∧
      (∑ e, if marks e = true then cost e else 0) ≤ (2 * p) * ∑ e, cost e := by
  obtain ⟨d₁, hd₁⟩ := tolerant_sampling_parameters_uniform A
  obtain ⟨d₂, hd₂⟩ := seed_event_parameters_uniform A h t (5 * baselineSampleConstant A)
    (mul_nonneg (by norm_num) (baselineSampleConstant_pos A).le) hh
  refine ⟨max d₁ d₂, ?_⟩
  intro d hd W I _ _ _ _ k D hdk hdD hDpow F _ H J _ _ hJ hF hhost q₁ q₂ r hq₁ hq₂ hq₁d hq₂d
    T p a u hp₀ hp₁ ha C B hB hsize hocc hprob cost hcost
  obtain ⟨hd1, _, _, he, _, _, _, _, hsk, hseed, _⟩ :=
    hd₁ d ((le_max_left _ _).trans hd) D k hdD hDpow hdk
  obtain ⟨ν, hν, hhalf, hincidence, hsizegap, hfactor⟩ :=
    hd₂ d ((le_max_right _ _).trans hd) k D (tolerantSamplingSeed A d k) q₁ q₂ hdk
      (hd1.trans hdD) hDpow hsk hseed hq₁ hq₂ hq₁d hq₂d a ha
  apply exists_seed_matching_marks F H J hJ D D hF hhost (hd1.trans hdD) (hd1.trans hdD)
    (tolerantSamplingSeed A d k) r (1 - 4 * tolerantSamplingError d) T (by linarith)
    C B h q₁ q₂ (D ^ t) hB hsize hocc p a ν u hp₀ hp₁ hν hprob hhalf
    ?_ ?_ hfactor cost hcost
  · simpa only [seedEventCountBound, seedAssignmentCountBound, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
      zero_add, one_pow, mul_one] using hincidence
  · simpa only [seedEventSupportBound, Fintype.card_fin] using hsizegap

/-- The uniform event budget applies to any seed-anchored candidate
lists satisfying the same size and coordinate-incidence bounds. -/
theorem uniform_seed_marking_for_lists (A h t : ℕ) (hh : 1 ≤ h) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W I : Type*)
    [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I],
    ∀ k D : ℕ, d ≤ k → d ≤ D → D ≤ d ^ A →
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj],
    J ≤ H → (∀ v, F.degree v ≤ D) → (∀ w, H.degree w ≤ D) →
    ∀ q₁ q₂ r : ℕ, 1 ≤ q₁ → 1 ≤ q₂ → q₁ ≤ d → q₂ ≤ d →
    ∀ (τ T p a u : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 0 < τ → seedEventExponent d k ≤ a →
    ∀ L : SeedDescription F H (tolerantSamplingSeed A d k) → Fin k → Finset W,
    (∀ c v, L c v ⊆ seedCandidateList F H J (tolerantSamplingSeed A d k) τ c v) →
    ∀ (C : Finset (SeedDescription F H (tolerantSamplingSeed A d k))) (B : I → Finset W),
    (∀ i, (B i).card ≤ q₂) → (∀ c : C, ∀ v, (L c.val v).card ≤ q₁) →
    (∀ c : C, ∀ v w, w ∈ L c.val v → (Finset.univ.filter (fun i => w ∈ B i)).card ≤ D ^ t) →
    (∀ c : C, (bitProductMeasure (Fin h × I) p hp₀ hp₁).real
      (thickMatchingEvent J (L c.val) r T B h u) ≤ Real.exp (-a)) →
    ∀ cost : (Fin h × I) → ℝ, (∀ e, 0 ≤ cost e) →
    ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (L c.val) r T B h u) ∧
      (∑ e, if marks e = true then cost e else 0) ≤ (2 * p) * ∑ e, cost e := by
  obtain ⟨d₁, hd₁⟩ := tolerant_sampling_parameters_uniform A
  obtain ⟨d₂, hd₂⟩ := seed_event_parameters_uniform A h t (5 * baselineSampleConstant A)
    (mul_nonneg (by norm_num) (baselineSampleConstant_pos A).le) hh
  refine ⟨max d₁ d₂, ?_⟩
  intro d hd W I _ _ _ _ k D hdk hdD hDpow F _ H J _ _ hJ hF hhost q₁ q₂ r hq₁ hq₂ hq₁d hq₂d
    τ T p a u hp₀ hp₁ hτ ha L hL C B hB hsize hocc hprob cost hcost
  obtain ⟨hd1, _, _, _, _, _, _, _, hsk, hseed, _⟩ :=
    hd₁ d ((le_max_left _ _).trans hd) D k hdD hDpow hdk
  obtain ⟨ν, hν, hhalf, hincidence, hsizegap, hfactor⟩ :=
    hd₂ d ((le_max_right _ _).trans hd) k D (tolerantSamplingSeed A d k) q₁ q₂ hdk
      (hd1.trans hdD) hDpow hsk hseed hq₁ hq₂ hq₁d hq₂d a ha
  apply exists_seed_matching_marks_for_lists F H J hJ D D hF hhost (hd1.trans hdD) (hd1.trans hdD)
    (tolerantSamplingSeed A d k) r τ T hτ L hL C B h q₁ q₂ (D ^ t) hB hsize hocc
    p a ν u hp₀ hp₁ hν hprob hhalf ?_ ?_ hfactor cost hcost
  · simpa only [seedEventCountBound, seedAssignmentCountBound, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat,
      zero_add, one_pow, mul_one] using hincidence
  · simpa only [seedEventSupportBound, Fintype.card_fin] using hsizegap

end Erdos911
