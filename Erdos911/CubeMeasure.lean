import Erdos911.CubeWeights
import Erdos911.ReadBound
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory

namespace Erdos911

noncomputable def bernoulliMarginal (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : Measure Bool :=
  ProbabilityTheory.bernoulliMeasure true false ⟨p, hp₀, hp₁⟩

instance bernoulliMarginal_isProbabilityMeasure (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMarginal p hp₀ hp₁) := by
  unfold bernoulliMarginal
  infer_instance

noncomputable def bernoulliCubeMeasure {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) : Measure (Fin n → Bool) :=
  Measure.pi (fun j => bernoulliMarginal (p j) (hp₀ j) (hp₁ j))

instance bernoulliCubeMeasure_isProbabilityMeasure {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) :
    IsProbabilityMeasure (bernoulliCubeMeasure p hp₀ hp₁) := by
  unfold bernoulliCubeMeasure
  infer_instance

theorem bernoulliMarginal_real_singleton (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (b : Bool) :
    (bernoulliMarginal p hp₀ hp₁).real {b} = bernoulliWeight p b := by
  cases b <;> simp [bernoulliMarginal, bernoulliWeight]

theorem bernoulliCubeMeasure_real_singleton {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (ω : Fin n → Bool) :
    (bernoulliCubeMeasure p hp₀ hp₁).real {ω} = cubeWeight p ω := by
  have hset : ({ω} : Set (Fin n → Bool)) = Set.univ.pi (fun j => ({ω j} : Set Bool)) := by
    ext ω'
    simp [Set.mem_pi, funext_iff]
  calc
    (bernoulliCubeMeasure p hp₀ hp₁).real {ω} =
        ∏ j, (bernoulliMarginal (p j) (hp₀ j) (hp₁ j)).real {ω j} := by
      simp only [Measure.real, bernoulliCubeMeasure, hset, Measure.pi_pi, ENNReal.toReal_prod]
    _ = cubeWeight p ω := by
      simp only [cubeWeight, bernoulliMarginal_real_singleton]

/-- The recursive cube probability agrees with the usual product measure. -/
theorem cubeProbability_eq_measureReal {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (A : Set (Fin n → Bool)) :
    cubeProbability p A = (bernoulliCubeMeasure p hp₀ hp₁).real A := by
  classical
  let S : Finset (Fin n → Bool) := Finset.univ.filter (fun ω => ω ∈ A)
  have hAS : A = (S : Set (Fin n → Bool)) := by ext ω; simp [S]
  calc
    cubeProbability p A = ∑ ω ∈ S, cubeWeight p ω := cubeProbability_eq_sum p A
    _ = ∑ ω ∈ S, (bernoulliCubeMeasure p hp₀ hp₁).real {ω} := by
      apply Finset.sum_congr rfl
      intro ω _
      exact (bernoulliCubeMeasure_real_singleton p hp₀ hp₁ ω).symm
    _ = (bernoulliCubeMeasure p hp₀ hp₁).real (S : Set (Fin n → Bool)) :=
      sum_measureReal_singleton S
    _ = (bernoulliCubeMeasure p hp₀ hp₁).real A := by rw [← hAS]

theorem cubeMean_eq_integral {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (f : (Fin n → Bool) → ℝ) :
    cubeMean p f = ∫ ω, f ω ∂bernoulliCubeMeasure p hp₀ hp₁ := by
  rw [cubeMean_eq_weightedMean]
  symm
  rw [integral_fintype .of_finite]
  simp only [weightedMean, smul_eq_mul, bernoulliCubeMeasure_real_singleton]

/-- The read-r bound expressed directly using Mathlib's product Bernoulli
measure and Bochner expectations. -/
theorem read_lower_tail_measure {n : ℕ} {κ : Type*} [Fintype κ]
    (p : Fin n → ℝ) (X : κ → (Fin n → Bool) → ℝ)
    (D : κ → Finset (Fin n)) (r : ℕ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (hr : 0 < r)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hD : ∀ i, FunctionDependsOn (X i) (D i))
    (hread : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ r) :
    (bernoulliCubeMeasure p hp₀ hp₁).real
      {ω | (∑ i, X i ω) ≤ (∑ i, ∫ ω, X i ω ∂bernoulliCubeMeasure p hp₀ hp₁) / 2} ≤
      Real.exp (-(∑ i, ∫ ω, X i ω ∂bernoulliCubeMeasure p hp₀ hp₁) / (8 * r)) := by
  simpa only [cubeProbability_eq_measureReal p hp₀ hp₁, cubeMean_eq_integral p hp₀ hp₁] using
    read_lower_tail p X D r hp₀ hp₁ hr hX hD hread

end Erdos911
