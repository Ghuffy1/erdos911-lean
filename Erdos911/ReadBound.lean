import Erdos911.CubeFinner
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos911

theorem prod_exp_scaled {κ : Type*} [Fintype κ] (c : ℝ) (a : κ → ℝ) :
    (∏ i, Real.exp (c * a i)) = Real.exp (c * ∑ i, a i) := by
  rw [← Real.exp_sum, ← Finset.mul_sum]

theorem cubeMean_exp_indicator_mul {n : ℕ} (p : Fin n → ℝ)
    (X : (Fin n → Bool) → ℝ) (t : ℝ) (hX : ∀ ω, X ω = 0 ∨ X ω = 1) :
    cubeMean p (fun ω => Real.exp (t * X ω)) =
      1 + (Real.exp t - 1) * cubeMean p X := by
  have hpoint : (fun ω => Real.exp (t * X ω)) =
      (fun ω => 1 + (Real.exp t - 1) * X ω) := by
    funext ω
    rcases hX ω with h | h <;> rw [h] <;> simp
  rw [hpoint, cubeMean_add, cubeMean_const, cubeMean_const_mul]

theorem cubeMean_exp_indicator {n : ℕ} (p : Fin n → ℝ)
    (X : (Fin n → Bool) → ℝ) (hX : ∀ ω, X ω = 0 ∨ X ω = 1) :
    cubeMean p (fun ω => Real.exp (-X ω)) =
      1 - (1 - Real.exp (-1)) * cubeMean p X := by
  have hco : Real.exp (-1) - 1 = -(1 - Real.exp (-1)) := by ring
  simpa only [neg_one_mul, hco, neg_mul, sub_eq_add_neg, one_mul] using
    cubeMean_exp_indicator_mul p X (-1) hX

/-- Exponential-moment bound for indicators with at most r readers per
coordinate. This is the product-Hölder step of the lower-tail estimate. -/
theorem read_mgf {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℝ) (X : κ → (Fin n → Bool) → ℝ)
    (D : κ → Finset (Fin n)) (r : ℕ) (t : ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (hr : 0 < r)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hD : ∀ i, FunctionDependsOn (X i) (D i))
    (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ r) :
    cubeMean p (fun ω => Real.exp (t * (∑ i, X i ω) / r)) ≤
      Real.exp ((Real.exp t - 1) * (∑ i, cubeMean p (X i)) / r) := by
  classical
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  let F : κ → (Fin n → Bool) → ℝ := fun i ω => Real.exp (t * X i ω)
  let w : κ → ℝ := fun _ => 1 / (r : ℝ)
  have hF : ∀ i ω, 0 < F i ω := fun i ω => Real.exp_pos _
  have hFdep : ∀ i, FunctionDependsOn (F i) (D i) := by
    intro i ω ω' heq
    dsimp [F]
    rw [hD i ω ω' heq]
  have hw : ∀ i, 0 ≤ w i := fun _ => (div_pos zero_lt_one hrreal).le
  have hbudget : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => j ∈ D i), w i ≤ 1 := by
    intro j
    change (∑ i ∈ Finset.univ.filter (fun i => j ∈ D i), 1 / (r : ℝ)) ≤ 1
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [mul_one_div]
    exact (div_le_one hrreal).mpr (by exact_mod_cast hread j)
  have hfinner := cube_finner n p F D w hp₀ hp₁ hF hFdep hw hbudget
  have hleft : (fun ω => ∏ i, (F i ω) ^ (w i)) =
      (fun ω => Real.exp (t * (∑ i, X i ω) / r)) := by
    funext ω
    calc
      (∏ i, (F i ω) ^ (w i)) = ∏ i, Real.exp ((t / (r : ℝ)) * X i ω) := by
        apply Finset.prod_congr rfl
        intro i _
        dsimp [F, w]
        rw [← Real.exp_mul]
        congr 1
        ring
      _ = Real.exp ((t / (r : ℝ)) * ∑ i, X i ω) := prod_exp_scaled _ _
      _ = Real.exp (t * (∑ i, X i ω) / r) := by congr 1; ring
  rw [hleft] at hfinner
  have hfactor : ∀ i, (cubeMean p (F i)) ^ (w i) ≤
      Real.exp (((Real.exp t - 1) / r) * cubeMean p (X i)) := by
    intro i
    have hmean : 0 < cubeMean p (F i) := cubeMean_pos p hp₀ hp₁ (hF i)
    have hupper : cubeMean p (F i) ≤
        Real.exp ((Real.exp t - 1) * cubeMean p (X i)) := by
      rw [show F i = (fun ω => Real.exp (t * X i ω)) from rfl,
        cubeMean_exp_indicator_mul p (X i) t (hX i)]
      have h := Real.add_one_le_exp ((Real.exp t - 1) * cubeMean p (X i))
      linarith
    have hpow := Real.rpow_le_rpow hmean.le hupper (hw i)
    convert hpow using 1
    dsimp [w]
    rw [← Real.exp_mul]
    congr 1
    ring
  calc
    cubeMean p (fun ω => Real.exp (t * (∑ i, X i ω) / r)) ≤
        ∏ i, (cubeMean p (F i)) ^ (w i) := hfinner
    _ ≤ ∏ i, Real.exp (((Real.exp t - 1) / r) * cubeMean p (X i)) :=
      Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (cubeMean_pos p hp₀ hp₁ (hF i)).le _)
        (fun i _ => hfactor i)
    _ = Real.exp ((Real.exp t - 1) * (∑ i, cubeMean p (X i)) / r) := by
      rw [prod_exp_scaled]
      congr 1
      ring

theorem read_indicator_mgf {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℝ) (X : κ → (Fin n → Bool) → ℝ)
    (D : κ → Finset (Fin n)) (r : ℕ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (hr : 0 < r)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hD : ∀ i, FunctionDependsOn (X i) (D i))
    (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ r) :
    cubeMean p (fun ω => Real.exp (-(∑ i, X i ω) / r)) ≤
      Real.exp (-(1 - Real.exp (-1)) * (∑ i, cubeMean p (X i)) / r) := by
  have hco : Real.exp (-1) - 1 = -(1 - Real.exp (-1)) := by ring
  simpa only [neg_one_mul, hco] using read_mgf p X D r (-1) hp₀ hp₁ hr hX hD hread

theorem read_tail_constant : (1 : ℝ) / 8 ≤ 1 - Real.exp (-1) - 1 / 2 := by
  have he : (8 : ℝ) / 3 < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hpos : 0 < Real.exp 1 := Real.exp_pos _
  have hinv : 1 / Real.exp 1 < (3 : ℝ) / 8 := by
    apply (div_lt_iff₀ hpos).mpr
    nlinarith
  rw [Real.exp_neg, ← one_div]
  linarith

/-- The read-r lower-tail bound, uniformly over the number of indicators and
independent Bernoulli coordinates. -/
theorem read_lower_tail {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℝ) (X : κ → (Fin n → Bool) → ℝ)
    (D : κ → Finset (Fin n)) (r : ℕ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (hr : 0 < r)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hD : ∀ i, FunctionDependsOn (X i) (D i))
    (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ r) :
    cubeProbability p {ω | (∑ i, X i ω) ≤ (∑ i, cubeMean p (X i)) / 2} ≤
      Real.exp (-(∑ i, cubeMean p (X i)) / (8 * r)) := by
  classical
  let μ : ℝ := ∑ i, cubeMean p (X i)
  let A : Set (Fin n → Bool) := {ω | (∑ i, X i ω) ≤ μ / 2}
  let t : ℝ := Real.exp (-μ / (2 * r))
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun i _ =>
    cubeMean_nonneg p hp₀ hp₁ (fun ω => by rcases hX i ω with h | h <;> simp [h]))
  have hpoint : ∀ ω, t * A.indicator (fun _ => (1 : ℝ)) ω ≤
      Real.exp (-(∑ i, X i ω) / r) := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, mul_one]
      apply Real.exp_le_exp.mpr
      have hsum : (∑ i, X i ω) ≤ μ / 2 := hω
      have hscaled : (∑ i, X i ω) / r ≤ μ / (2 * r) := by
        simpa only [div_div] using div_le_div_of_nonneg_right hsum hrreal.le
      simpa only [neg_div] using neg_le_neg hscaled
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact (Real.exp_pos _).le
  have hmarkov := cubeMean_mono p hp₀ hp₁ hpoint
  rw [cubeMean_const_mul] at hmarkov
  have hmgf := read_indicator_mgf p X D r hp₀ hp₁ hr hX hD hread
  have ht : 0 < t := Real.exp_pos _
  have hbound : cubeProbability p A ≤ Real.exp (-(1 - Real.exp (-1)) * μ / r) / t := by
    apply (le_div_iff₀ ht).mpr
    have hproduct : cubeProbability p A * t ≤
        cubeMean p (fun ω => Real.exp (-(∑ i, X i ω) / r)) := by
      simpa only [cubeProbability, mul_comm] using hmarkov
    exact hproduct.trans hmgf
  have hexponent : -(1 - Real.exp (-1)) * μ / r - (-μ / (2 * r)) =
      -(1 - Real.exp (-1) - 1 / 2) * μ / r := by ring
  dsimp [t] at hbound
  rw [← Real.exp_sub, hexponent] at hbound
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right read_tail_constant hμ) hrreal.le
  convert neg_le_neg hscaled using 1 <;> ring

end Erdos911
