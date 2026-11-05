import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

namespace Erdos911

/-- Count values above a threshold by controlling the contribution below it. -/
theorem threshold_count_of_moment_bound {ι : Type*} (S : Finset ι)
    (f : ι → ℝ) (p : ℕ) (a k D T : ℝ)
    (hf₀ : ∀ x ∈ S, 0 ≤ f x) (hf₁ : ∀ x ∈ S, f x ≤ 1)
    (hk : 0 ≤ k) (hD : ∑ x ∈ S, f x ≤ D)
    (hT : T ≤ ∑ x ∈ S, (f x) ^ p)
    (hlow : ∀ x ∈ S, f x < a → (f x) ^ p ≤ k * f x) :
    T ≤ (S.filter fun x => a ≤ f x).card + k * D := by
  classical
  have hpoint : ∀ x ∈ S, (f x) ^ p ≤
      (if a ≤ f x then (1 : ℝ) else 0) + k * f x := by
    intro x hx
    by_cases ha : a ≤ f x
    · simp only [ite_eq_left ha]
      exact (pow_le_one₀ (hf₀ x hx) (hf₁ x hx)).trans
        (le_add_of_nonneg_right (mul_nonneg hk (hf₀ x hx)))
    · simp only [ite_eq_right ha, zero_add]
      exact hlow x hx (lt_of_not_ge ha)
  calc
    T ≤ ∑ x ∈ S, (f x) ^ p := hT
    _ ≤ ∑ x ∈ S, ((if a ≤ f x then (1 : ℝ) else 0) + k * f x) :=
      Finset.sum_le_sum hpoint
    _ = (S.filter fun x => a ≤ f x).card + k * ∑ x ∈ S, f x := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ (S.filter fun x => a ≤ f x).card + k * D := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hD hk)

/-- Analytic core of the candidate-list center estimate with every numerical
hypothesis explicit. The decay condition is essential. -/
theorem centers_from_moments {ι : Type*} (S : Finset ι)
    (f : ι → ℝ) (r : ℕ) (a D T : ℝ)
    (ha : 0 ≤ a) (hf₀ : ∀ x ∈ S, 0 ≤ f x)
    (hf₁ : ∀ x ∈ S, f x ≤ 1)
    (hD : ∑ x ∈ S, f x ≤ D)
    (hT : T ≤ ∑ x ∈ S, (f x) ^ (r + 1))
    (hdecay : D * a ^ r ≤ T / 2) :
    T / 2 ≤ (S.filter fun x => a ≤ f x).card := by
  classical
  have hlow : ∀ x ∈ S, f x < a → (f x) ^ (r + 1) ≤ a ^ r * f x := by
    intro x hx hxa
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hf₀ x hx) hxa.le r) (hf₀ x hx)
  have hcount := threshold_count_of_moment_bound S f (r + 1) a (a ^ r) D T
    hf₀ hf₁ (pow_nonneg ha _) hD hT hlow
  nlinarith

end Erdos911
