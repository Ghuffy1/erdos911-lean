import Erdos911.FamilyListEvents
import Erdos911.CopyCandidateMatching
import Erdos911.RobustNeighborhoodLists

namespace Erdos911

noncomputable def thickMatchingEvent {V I W : Type*}
    [Fintype V] [Fintype I] [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ)
    (B : I → Finset W) (h : ℕ) (u : ℝ) : Set ((Fin h × I) → Bool) :=
  let matching := maximumListMatching (fun v : thickCandidateRoles J L s T => L v.val)
  fewBlockedLists B h (fun k : matchedRoles matching => L k.val.val) u

theorem thickMatchingEvent_depends {V I W : Type*}
    [Fintype V] [Fintype I] [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ)
    (B : I → Finset W) (h : ℕ) (u : ℝ) :
    DependsOnlyOn (thickMatchingEvent J L s T B h u) (familyListCoordinates B h L) := by
  exact fewBlockedLists_depends B h L
    (fun k : matchedRoles (maximumListMatching (fun v : thickCandidateRoles J L s T => L v.val)) =>
      k.val.val) u

theorem thickMatchingEvent_probability {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (X : Finset W) (L : V → Finset W)
    (s t D q h m : ℕ) (D₀ T R θ p β u : ℝ)
    [DecidableRel (highCodegreeGraph J R).Adj]
    (hs : 2 ≤ s) (ht : 0 < t) (hq : 0 < q)
    (hLX : ∀ v : thickCandidateRoles J L s T, L v.val ⊆ X)
    (hD₀ : 0 < D₀) (hT : 0 < T) (hR : 0 ≤ R) (hRT : R < T)
    (hD : ∀ w, J.degree w ≤ D)
    (hsingle : ∀ x ∈ X, ((commonCenters J.Adj {x}).card : ℝ) ≤ D₀)
    (hQ : ∀ x ∈ X, (highCodegreeGraph J R).degree x < q)
    (hgap : (D : ℝ) ^ 2 * R ^ t ≤ (T / 4) ^ t / 2)
    (hθ : Real.log (2 * D₀ / T) / ((s - 1 : ℕ) : ℝ) ≤ θ)
    (hθ₀ : 0 ≤ θ) (hθhalf : θ ≤ 1 / 2)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hβ : 0 ≤ β)
    (hβbound : β ≤ 1 - Real.exp (-p * ((T / 4) ^ t / 2)))
    (hinitial : ∀ v : thickCandidateRoles J L s T, ((t : ℝ) * θ) ^ h * ((L v.val).card : ℝ) ≤ s)
    (hmass : m ≤ (matchedRoles
      (maximumListMatching (fun v : thickCandidateRoles J L s T => L v.val))).card)
    (hu : u ≤ β ^ (h + 1) * m / 2) :
    (bitProductMeasure (Fin (h + 1) × (Fin t → W)) p hp₀ hp₁).real
      (thickMatchingEvent J L s T (boundedNeighborhoodTupleBlock J X q) (h + 1) u) ≤
      Real.exp (-(β ^ (h + 1) * m) / (8 * (q * q : ℕ))) := by
  classical
  let A := fun v : thickCandidateRoles J L s T => L v.val
  let matching := maximumListMatching A
  let K := matchedRoles matching
  let lists := fun k : K => L k.val.val
  have hcard : (m : ℝ) ≤ Fintype.card K := by
    have hcardNat : m ≤ Fintype.card K := by simpa only [K, Fintype.card_coe] using hmass
    exact_mod_cast hcardNat
  have hscale := mul_le_mul_of_nonneg_left hcard (pow_nonneg hβ (h + 1))
  have hprob := robust_neighborhood_list_bound J X lists s t D q h D₀ T R θ p β u
    hs ht hq (fun k => hLX k.val) hD₀ hT hR hRT hD hsingle
    (fun k => thickCandidateRoles_common J L s T (by omega) k.val) hQ hgap hθ hθ₀ hθhalf
    hp₀ hp₁ hβ hβbound (fun k => hinitial k.val)
    (matchedRepresentative matching) (matchedRepresentative_injective A matching (maximumListMatching_spec A).1)
    (matchedRepresentative_mem A matching (maximumListMatching_spec A).1)
    (hu.trans (by linarith))
  apply hprob.trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg hscale) (by positivity)

end Erdos911
