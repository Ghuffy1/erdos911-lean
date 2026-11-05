import Erdos911.NormalizationAsymptotics

namespace Erdos911

def unbalancedRightDegree (q : ℕ) : ℕ := q / 1048576

def unbalancedLeftFloor (p : ℕ) : ℕ := p / 8

noncomputable def unbalancedDegreeCap (Λ : ℝ) (p : ℕ) : ℕ := Nat.ceil (4 * Λ * p)

structure UnbalancedNormalizationBounds (q p : ℕ) (Λ : ℝ) : Prop where
  right_positive : 1 ≤ unbalancedRightDegree q
  right_fraction : (1 / 4194304 : ℝ) ≤ (unbalancedRightDegree q : ℝ) / (2 * q)
  mean_lower : (1 / 67108864 : ℝ) * p ≤
    (unbalancedRightDegree q : ℝ) / (2 * q) * unbalancedLeftFloor p
  left_lower : (p : ℝ) / 134217728 ≤
    (unbalancedRightDegree q : ℝ) / (2 * q) * unbalancedLeftFloor p / 2
  cutoff_lower : 4 * Λ * p ≤ (unbalancedDegreeCap Λ p : ℝ)
  cutoff_upper : (unbalancedDegreeCap Λ p : ℝ) ≤ 5 * Λ * p
  dependency_upper : (unbalancedDegreeCap Λ p : ℝ) * (2 * q) ≤ 10 * (p : ℝ) ^ 2

/-- The left scale p can be arbitrarily large. Only q and the ratio
parameter Lambda enter its polynomial lower bound. -/
theorem unbalanced_normalization_bounds (q p : ℕ) (Λ : ℝ)
    (hq : 2097152 ≤ q) (hp : q ^ 3 ≤ p) (hΛ : 1 ≤ Λ) (hΛq : Λ ≤ (q : ℝ) ^ 2) :
    UnbalancedNormalizationBounds q p Λ := by
  have hqR : (2097152 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < q := by linarith
  have hq1 : 1 ≤ q := by omega
  have hqpow : q ≤ q ^ 3 := by simpa using Nat.pow_le_pow_right hq1 (show 1 ≤ 3 by omega)
  have hp16 : 16 ≤ p := by omega
  have hpR : (16 : ℝ) ≤ p := by exact_mod_cast hp16
  have hpp : (0 : ℝ) < p := by linarith
  have hfq : q ≤ 2097152 * unbalancedRightDegree q := by unfold unbalancedRightDegree; omega
  have hright : (1 / 4194304 : ℝ) ≤ (unbalancedRightDegree q : ℝ) / (2 * q) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (q : ℝ))).mpr
    have h : (q : ℝ) ≤ 2097152 * unbalancedRightDegree q := by exact_mod_cast hfq
    linarith only [h]
  have hfloor : (p : ℝ) / 16 ≤ unbalancedLeftFloor p := by
    have h : p ≤ 16 * unbalancedLeftFloor p := by unfold unbalancedLeftFloor; omega
    have hR : (p : ℝ) ≤ 16 * unbalancedLeftFloor p := by exact_mod_cast h
    linarith only [hR]
  have hmean : (1 / 67108864 : ℝ) * p ≤
      (unbalancedRightDegree q : ℝ) / (2 * q) * unbalancedLeftFloor p := by
    have h := mul_le_mul hright hfloor (show 0 ≤ (p : ℝ) / 16 by positivity)
      (show 0 ≤ (unbalancedRightDegree q : ℝ) / (2 * q) by positivity)
    nlinarith only [h]
  have hΛp : 1 ≤ Λ * p := one_le_mul_of_one_le_of_one_le hΛ (by linarith)
  have hcap : (unbalancedDegreeCap Λ p : ℝ) ≤ 5 * Λ * p := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ 4 * Λ * (p : ℝ) by positivity)).le
    change (unbalancedDegreeCap Λ p : ℝ) ≤ 4 * Λ * p + 1 at h
    nlinarith only [h, hΛp]
  have hdep : (unbalancedDegreeCap Λ p : ℝ) * (2 * q) ≤ 10 * (p : ℝ) ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hcap (show 0 ≤ 2 * (q : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hΛq (show 0 ≤ 10 * (p : ℝ) * q by positivity)
    have hpR' : (q : ℝ) ^ 3 ≤ p := by exact_mod_cast hp
    have h₃ := mul_le_mul_of_nonneg_right hpR' (show 0 ≤ 10 * (p : ℝ) by positivity)
    nlinarith only [h₁, h₂, h₃]
  exact ⟨by unfold unbalancedRightDegree; omega, hright, hmean, by linarith only [hmean],
    Nat.le_ceil _, hcap, hdep⟩

/-- A single threshold gives valid normalization probabilities uniformly
over every larger left degree scale p, even without a global degree bound. -/
theorem unbalanced_normalization_eventually :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ p : ℕ, q ^ 3 ≤ p → ∀ Λ : ℝ, 1 ≤ Λ → Λ ≤ (q : ℝ) ^ 2 →
      Real.exp 1 * Real.exp (-((unbalancedRightDegree q : ℝ) / (2 * q : ℕ) *
        unbalancedLeftFloor p) / 8) * ((unbalancedDegreeCap Λ p * (2 * q) : ℕ) + 1) ≤ 1 := by
  obtain ⟨x₀, hx₀⟩ := degree_normalization_eventually (c := 1 / 67108864) (K := 10) 2 (by norm_num)
  refine ⟨max 2097152 (Nat.ceil x₀), ?_⟩
  intro q hq p hp Λ hΛ hΛq
  have hqbase : 2097152 ≤ q := (le_max_left _ _).trans hq
  have hqp : q ≤ p := by
    have hq1 : 1 ≤ q := by omega
    have hqpow : q ≤ q ^ 3 := by simpa using Nat.pow_le_pow_right hq1 (show 1 ≤ 3 by omega)
    omega
  have hx : x₀ ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil x₀ ≤ p by omega))
  have h := unbalanced_normalization_bounds q p Λ hqbase hp hΛ hΛq
  apply hx₀ p hx (unbalancedRightDegree q) (unbalancedDegreeCap Λ p) (2 * q) (unbalancedLeftFloor p)
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using h.mean_lower
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using h.dependency_upper

end Erdos911
