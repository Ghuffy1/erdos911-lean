import Erdos911.ReadBound

namespace Erdos911

/-- Exponential Markov bound, with the threshold condition supplied on the
event to be estimated. -/
theorem cube_exponential_markov {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (Y : (Fin n → Bool) → ℝ) (A : Set (Fin n → Bool)) (a b : ℝ)
    (hA : ∀ ω ∈ A, a ≤ Y ω)
    (hmgf : cubeMean p (fun ω => Real.exp (Y ω)) ≤ Real.exp b) :
    cubeProbability p A ≤ Real.exp (b - a) := by
  classical
  have hpoint : ∀ ω, Real.exp a * A.indicator (fun _ => (1 : ℝ)) ω ≤ Real.exp (Y ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, mul_one]
      exact Real.exp_le_exp.mpr (hA ω hω)
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact (Real.exp_pos _).le
  have hmean := cubeMean_mono p hp₀ hp₁ hpoint
  rw [cubeMean_const_mul] at hmean
  have hproduct : cubeProbability p A * Real.exp a ≤ Real.exp b := by
    have hfirst : cubeProbability p A * Real.exp a ≤ cubeMean p (fun ω => Real.exp (Y ω)) := by
      simpa only [cubeProbability, mul_comm] using hmean
    exact hfirst.trans hmgf
  have hdiv := (le_div_iff₀ (Real.exp_pos a)).mpr hproduct
  simpa only [Real.exp_sub] using hdiv

theorem exp_le_one_add_two_sq (t : ℝ) (_ht₀ : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.exp t ≤ 1 + t + 2 * t ^ 2 := by
  have hpos : 0 < 1 - t := by linarith
  have hmul : (1 - t) * Real.exp t ≤ 1 := by
    calc
      (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos t).le
        linarith [Real.add_one_le_exp (-t)]
      _ = 1 := by rw [← Real.exp_add]; simp
  have hreciprocal : Real.exp t ≤ 1 / (1 - t) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hmul)
  have hpoly : 1 / (1 - t) ≤ 1 + t + 2 * t ^ 2 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - 2 * t by linarith)]
  exact hreciprocal.trans hpoly

theorem exp_neg_le_one_sub_add_sq (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 - t + t ^ 2 := by
  have hpos : 0 < 1 + t := by linarith
  have hreciprocal : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hpos (by linarith [Real.add_one_le_exp t])
  have hpoly : 1 / (1 + t) ≤ 1 - t + t ^ 2 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg ht (sq_nonneg t)]
  exact hreciprocal.trans hpoly

/-- Upper additive tail with a deterministic bound M on the total mean.
For independent indicators take r = 1. -/
theorem read_upper_additive {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℝ) (X : κ → (Fin n → Bool) → ℝ)
    (D : κ → Finset (Fin n)) (r : ℕ) (M ε : ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (hr : 0 < r)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hD : ∀ i, FunctionDependsOn (X i) (D i))
    (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ r)
    (hM : (∑ i, cubeMean p (X i)) ≤ M) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    cubeProbability p {ω | (∑ i, cubeMean p (X i)) + ε * M ≤ ∑ i, X i ω} ≤
      Real.exp (-(ε ^ 2 * M) / (8 * r)) := by
  classical
  let μ := ∑ i, cubeMean p (X i)
  let t := ε / 4
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hμ : 0 ≤ μ := Finset.sum_nonneg fun i _ =>
    cubeMean_nonneg p hp₀ hp₁ (fun ω => by rcases hX i ω with h | h <;> simp [h])
  have ht₀ : 0 ≤ t := div_nonneg hε₀ (by norm_num)
  have ht₁ : t ≤ 1 / 2 := by dsimp [t]; linarith
  have hmgf := read_mgf p X D r t hp₀ hp₁ hr hX hD hread
  have hprob := cube_exponential_markov p hp₀ hp₁
    (fun ω => t * (∑ i, X i ω) / r)
    {ω | μ + ε * M ≤ ∑ i, X i ω}
    (t * (μ + ε * M) / r) ((Real.exp t - 1) * μ / r) ?_ hmgf
  · apply hprob.trans
    apply Real.exp_le_exp.mpr
    have hquad := mul_le_mul_of_nonneg_right (exp_le_one_add_two_sq t ht₀ ht₁) hμ
    have hM' : μ ≤ M := hM
    have hmass := mul_le_mul_of_nonneg_left hM' (show 0 ≤ 2 * t ^ 2 by positivity)
    have hnum : (Real.exp t - 1) * μ - t * (μ + ε * M) ≤ -(ε ^ 2 * M) / 8 := by
      dsimp [t] at hquad hmass ⊢
      nlinarith only [hquad, hmass]
    have hdiv := div_le_div_of_nonneg_right hnum hrreal.le
    convert hdiv using 1 <;> ring
  · intro ω hω
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω ht₀) hrreal.le

/-- Lower additive tail with the same mean cap, allowing overlap of read-r
indicator families. -/
theorem read_lower_additive {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℝ) (X : κ → (Fin n → Bool) → ℝ)
    (D : κ → Finset (Fin n)) (r : ℕ) (M ε : ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (hr : 0 < r)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hD : ∀ i, FunctionDependsOn (X i) (D i))
    (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ r)
    (hM : (∑ i, cubeMean p (X i)) ≤ M) (hε₀ : 0 ≤ ε) :
    cubeProbability p {ω | (∑ i, X i ω) ≤ (∑ i, cubeMean p (X i)) - ε * M} ≤
      Real.exp (-(ε ^ 2 * M) / (4 * r)) := by
  classical
  let μ := ∑ i, cubeMean p (X i)
  let t := ε / 2
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hμ : 0 ≤ μ := Finset.sum_nonneg fun i _ =>
    cubeMean_nonneg p hp₀ hp₁ (fun ω => by rcases hX i ω with h | h <;> simp [h])
  have ht : 0 ≤ t := div_nonneg hε₀ (by norm_num)
  have hmgf := read_mgf p X D r (-t) hp₀ hp₁ hr hX hD hread
  have hprob := cube_exponential_markov p hp₀ hp₁
    (fun ω => -t * (∑ i, X i ω) / r)
    {ω | (∑ i, X i ω) ≤ μ - ε * M}
    (-t * (μ - ε * M) / r) ((Real.exp (-t) - 1) * μ / r) ?_ hmgf
  · apply hprob.trans
    apply Real.exp_le_exp.mpr
    have hquad := mul_le_mul_of_nonneg_right (exp_neg_le_one_sub_add_sq t ht) hμ
    have hM' : μ ≤ M := hM
    have hmass := mul_le_mul_of_nonneg_left hM' (sq_nonneg t)
    have hnum : (Real.exp (-t) - 1) * μ + t * (μ - ε * M) ≤ -(ε ^ 2 * M) / 4 := by
      dsimp [t] at hquad hmass ⊢
      nlinarith only [hquad, hmass]
    have hdiv := div_le_div_of_nonneg_right hnum hrreal.le
    convert hdiv using 1 <;> ring
  · intro ω hω
    have hmul := mul_le_mul_of_nonneg_left hω ht
    exact div_le_div_of_nonneg_right (by nlinarith) hrreal.le

end Erdos911
