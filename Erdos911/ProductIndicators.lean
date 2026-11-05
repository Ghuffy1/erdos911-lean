import Erdos911.SampleConcentration
import Mathlib.MeasureTheory.Measure.Dirac.Basic

open MeasureTheory

namespace Erdos911

/-- A probability measure on Bool is determined by its mass at true. -/
theorem bool_measure_eq_bernoulli (μ : Measure Bool) [IsProbabilityMeasure μ]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hp : μ.real {true} = p) :
    μ = bernoulliMarginal p hp₀ hp₁ := by
  apply Measure.ext_of_measureReal_singleton
  intro b
  rw [bernoulliMarginal_real_singleton]
  cases b with
  | false =>
    have hc : ({true} : Set Bool)ᶜ = {false} := by
      ext b
      cases b <;> simp
    have htotal := measureReal_add_measureReal_compl (μ := μ)
      (measurableSet_singleton true)
    rw [hc, hp] at htotal
    simp only [probReal_univ] at htotal
    change μ.real {false} = 1 - p
    linarith
  | true => exact hp

/-- Taking one Boolean indicator from each independent coordinate gives the
product Bernoulli distribution with the corresponding marginal probabilities. -/
theorem product_indicators_map {n : ℕ} {β : Fin n → Type*}
    [∀ j, MeasurableSpace (β j)]
    (μ : ∀ j, Measure (β j)) [∀ j, IsProbabilityMeasure (μ j)]
    (f : ∀ j, β j → Bool) (hf : ∀ j, Measurable (f j))
    (p : Fin n → ℝ) (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hp : ∀ j, (μ j).real ((f j) ⁻¹' {true}) = p j) :
    (Measure.pi μ).map (fun ω j => f j (ω j)) = bernoulliCubeMeasure p hp₀ hp₁ := by
  rw [Measure.pi_map_pi (fun j => (hf j).aemeasurable)]
  unfold bernoulliCubeMeasure
  congr 1
  funext j
  apply bool_measure_eq_bernoulli ((μ j).map (f j)) (p j) (hp₀ j) (hp₁ j)
  simpa only [Measure.real, Measure.map_apply (hf j) (measurableSet_singleton true)]
    using hp j

theorem product_indicator_probability {n : ℕ} {β : Fin n → Type*}
    [∀ j, MeasurableSpace (β j)]
    (μ : ∀ j, Measure (β j)) [∀ j, IsProbabilityMeasure (μ j)]
    (f : ∀ j, β j → Bool) (hf : ∀ j, Measurable (f j))
    (p : Fin n → ℝ) (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hp : ∀ j, (μ j).real ((f j) ⁻¹' {true}) = p j)
    (A : Set (Fin n → Bool)) :
    (Measure.pi μ).real ((fun ω j => f j (ω j)) ⁻¹' A) =
      (bernoulliCubeMeasure p hp₀ hp₁).real A := by
  have hmap : Measurable (fun (ω : ∀ j, β j) j => f j (ω j)) :=
    measurable_pi_iff.mpr (fun j => (hf j).comp (measurable_pi_apply j))
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [← product_indicators_map μ f hf p hp₀ hp₁ hp]
  simp only [Measure.real, Measure.map_apply hmap hA]

/-- Lower-tail estimate for indicators of independent finite-valued choices. -/
theorem product_indicator_lower_tail {n : ℕ} {β : Fin n → Type*}
    [∀ j, MeasurableSpace (β j)]
    (μ : ∀ j, Measure (β j)) [∀ j, IsProbabilityMeasure (μ j)]
    (f : ∀ j, β j → Bool) (hf : ∀ j, Measurable (f j))
    (p : Fin n → ℝ) (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hp : ∀ j, (μ j).real ((f j) ⁻¹' {true}) = p j)
    (U : Finset (Fin n)) :
    (Measure.pi μ).real
        {ω | sampleCount U (fun j => f j (ω j)) ≤ (∑ j : U, p j) / 2} ≤
      Real.exp (-(∑ j : U, p j) / 8) := by
  have h := read_lower_tail p (fun j : U => coordinateIndicator j.val)
    (fun j : U => ({j.val} : Finset (Fin n))) 1 hp₀ hp₁ (by decide)
    (fun j => coordinateIndicator_values j.val) (fun j => coordinateIndicator_depends j.val)
    (sample_coordinate_read_bound U)
  have htail : (bernoulliCubeMeasure p hp₀ hp₁).real
      {ω | sampleCount U ω ≤ (∑ j : U, p j) / 2} ≤
        Real.exp (-(∑ j : U, p j) / 8) := by
    simpa only [cubeProbability_eq_measureReal p hp₀ hp₁, cubeMean_coordinate,
      Nat.cast_one, mul_one, sampleCount] using h
  rw [← product_indicator_probability μ f hf p hp₀ hp₁ hp] at htail
  exact htail

end Erdos911
