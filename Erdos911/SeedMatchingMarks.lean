import Erdos911.ThickMatchingEvents
import Erdos911.ExponentialEventMarking
import Erdos911.UnmarkedSetAvoidance

namespace Erdos911

/-- Incidence bounds for actual seed descriptions make it possible to
avoid all their matching events within twice the independent cost. -/
theorem exists_seed_matching_marks_for_lists {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s r : ℕ) (τ T : ℝ) (hτ : 0 < τ)
    (L : SeedDescription F H s → V → Finset W)
    (hL : ∀ c v, L c v ⊆ seedCandidateList F H J s τ c v)
    (C : Finset (SeedDescription F H s)) (B : I → Finset W) (h q₁ q₂ N : ℕ)
    (hB : ∀ i, (B i).card ≤ q₂)
    (hsize : ∀ c : C, ∀ v, (L c.val v).card ≤ q₁)
    (hocc : ∀ c : C, ∀ v w, w ∈ L c.val v →
      (Finset.univ.filter (fun i => w ∈ B i)).card ≤ N)
    (p a ν u : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hν : 0 ≤ ν)
    (hprob : ∀ c : C, (bitProductMeasure (Fin h × I) p hp₀ hp₁).real
      (thickMatchingEvent J (L c.val) r T B h u) ≤ Real.exp (-a))
    (hhalf : Real.exp (-a / 2) ≤ 1 / 2)
    (hincidence : (q₂ * (Fintype.card V * (D + 1) *
      ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)) : ℝ) * Real.exp (-a / 2) ≤ ν)
    (hsizegap : 4 * ν * (h * Fintype.card V * q₁ * N : ℕ) ≤ a)
    (hfactor : Real.exp (2 * ν) ≤ 2)
    (cost : (Fin h × I) → ℝ) (hcost : ∀ e, 0 ≤ cost e) :
    ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (L c.val) r T B h u) ∧
      (∑ e, if marks e = true then cost e else 0) ≤ (2 * p) * ∑ e, cost e := by
  classical
  let A := fun c : C => thickMatchingEvent J (L c.val) r T B h u
  let S := fun c : C => familyListCoordinates B h (L c.val)
  have hcount : ∀ e, (Finset.univ.filter (fun c : C => e ∈ S c)).card ≤
      q₂ * (Fintype.card V * (D + 1) * ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)) := by
    intro e
    apply (subtype_filter_card_le C (fun c => e ∈ familyListCoordinates B h (L c))).trans
    exact seed_family_coordinates_incidence F H J hJ Δ D hΔ hD hΔpos hDpos s τ hτ L hL B h q₂ hB e
  exact exists_exponential_event_marks A S
    (fun c => thickMatchingEvent_depends J (L c.val) r T B h u)
    (q₂ * (Fintype.card V * (D + 1) * ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)))
    (h * Fintype.card V * q₁ * N)
    (fun c => familyListCoordinates_card_le B h (L c.val) q₁ N (hsize c) (hocc c))
    hcount p a ν hp₀ hp₁ hν hprob hhalf
    (by simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using hincidence)
    hsizegap hfactor cost hcost

theorem exists_seed_matching_marks {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s r : ℕ) (τ T : ℝ) (hτ : 0 < τ)
    (C : Finset (SeedDescription F H s)) (B : I → Finset W) (h q₁ q₂ N : ℕ)
    (hB : ∀ i, (B i).card ≤ q₂)
    (hsize : ∀ c : C, ∀ v, (unseededCandidateList F H J s τ c.val v).card ≤ q₁)
    (hocc : ∀ c : C, ∀ v w, w ∈ unseededCandidateList F H J s τ c.val v →
      (Finset.univ.filter (fun i => w ∈ B i)).card ≤ N)
    (p a ν u : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hν : 0 ≤ ν)
    (hprob : ∀ c : C, (bitProductMeasure (Fin h × I) p hp₀ hp₁).real
      (thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B h u) ≤ Real.exp (-a))
    (hhalf : Real.exp (-a / 2) ≤ 1 / 2)
    (hincidence : (q₂ * (Fintype.card V * (D + 1) *
      ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)) : ℝ) * Real.exp (-a / 2) ≤ ν)
    (hsizegap : 4 * ν * (h * Fintype.card V * q₁ * N : ℕ) ≤ a)
    (hfactor : Real.exp (2 * ν) ≤ 2)
    (cost : (Fin h × I) → ℝ) (hcost : ∀ e, 0 ≤ cost e) :
    ∃ marks : (Fin h × I) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B h u) ∧
      (∑ e, if marks e = true then cost e else 0) ≤ (2 * p) * ∑ e, cost e := by
  exact exists_seed_matching_marks_for_lists F H J hJ Δ D hΔ hD hΔpos hDpos s r τ T hτ
    (unseededCandidateList F H J s τ) (fun c v => unseededCandidateList_subset F H J s τ c v)
    C B h q₁ q₂ N hB hsize hocc p a ν u hp₀ hp₁ hν hprob hhalf hincidence hsizegap hfactor cost hcost

end Erdos911
