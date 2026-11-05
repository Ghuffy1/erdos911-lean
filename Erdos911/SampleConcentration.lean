import Erdos911.Concentration
import Erdos911.CubeMeasure

namespace Erdos911

def coordinateIndicator {n : ℕ} (j : Fin n) (ω : Fin n → Bool) : ℝ :=
  if ω j then 1 else 0

theorem coordinateIndicator_values {n : ℕ} (j : Fin n) (ω : Fin n → Bool) :
    coordinateIndicator j ω = 0 ∨ coordinateIndicator j ω = 1 := by
  cases h : ω j <;> simp [coordinateIndicator, h]

theorem coordinateIndicator_depends {n : ℕ} (j : Fin n) :
    FunctionDependsOn (coordinateIndicator j) {j} := by
  intro ω ω' heq
  unfold coordinateIndicator
  rw [heq j (Finset.mem_singleton_self _)]

theorem cubeMean_coordinate {n : ℕ} (p : Fin n → ℝ) (j : Fin n) :
    cubeMean p (coordinateIndicator j) = p j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    cases j using Fin.cases with
    | zero =>
      simp [coordinateIndicator, cubeMean_succ, bernoulliMean_eq, cubeMean_const]
    | succ j =>
      simp only [cubeMean_succ, coordinateIndicator, Fin.cons_succ, bernoulliMean_const]
      exact ih (fun k => p k.succ) j

def sampleCount {n : ℕ} (U : Finset (Fin n)) (ω : Fin n → Bool) : ℝ :=
  ∑ j : U, coordinateIndicator j ω

theorem sample_coordinate_read_bound {n : ℕ} (U : Finset (Fin n)) (j : Fin n) :
    (Finset.univ.filter (fun i : U => j ∈ ({i.val} : Finset (Fin n)))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi k hk
  apply Subtype.ext
  have hi' : j = i.val := Finset.mem_singleton.mp (Finset.mem_filter.mp hi).2
  have hk' : j = k.val := Finset.mem_singleton.mp (Finset.mem_filter.mp hk).2
  exact hi'.symm.trans hk'

/-- Both additive tails for the number of sampled vertices in a prescribed set.
The mean cap M may be taken from a larger set, as in the adaptive seed tests. -/
theorem sample_count_tails {n : ℕ} (p : Fin n → ℝ) (U : Finset (Fin n)) (M ε : ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hM : (∑ j : U, p j) ≤ M) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    (bernoulliCubeMeasure p hp₀ hp₁).real
        {ω | (∑ j : U, p j) + ε * M ≤ sampleCount U ω} ≤ Real.exp (-(ε ^ 2 * M) / 8) ∧
      (bernoulliCubeMeasure p hp₀ hp₁).real
        {ω | sampleCount U ω ≤ (∑ j : U, p j) - ε * M} ≤ Real.exp (-(ε ^ 2 * M) / 4) := by
  have hmean : (∑ j : U, cubeMean p (coordinateIndicator j.val)) ≤ M := by
    simpa only [cubeMean_coordinate] using hM
  constructor
  · have h := read_upper_additive p (fun j : U => coordinateIndicator j.val)
      (fun j : U => ({j.val} : Finset (Fin n))) 1 M ε hp₀ hp₁ (by decide)
      (fun j => coordinateIndicator_values j.val) (fun j => coordinateIndicator_depends j.val)
      (sample_coordinate_read_bound U) hmean hε₀ hε₁
    simpa only [cubeProbability_eq_measureReal p hp₀ hp₁, cubeMean_coordinate,
      Nat.cast_one, mul_one, sampleCount] using h
  · have h := read_lower_additive p (fun j : U => coordinateIndicator j.val)
      (fun j : U => ({j.val} : Finset (Fin n))) 1 M ε hp₀ hp₁ (by decide)
      (fun j => coordinateIndicator_values j.val) (fun j => coordinateIndicator_depends j.val)
      (sample_coordinate_read_bound U) hmean hε₀
    simpa only [cubeProbability_eq_measureReal p hp₀ hp₁, cubeMean_coordinate,
      Nat.cast_one, mul_one, sampleCount] using h

theorem sample_count_two_sided {n : ℕ} (p : Fin n → ℝ) (U : Finset (Fin n)) (M ε : ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hM : (∑ j : U, p j) ≤ M) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    (bernoulliCubeMeasure p hp₀ hp₁).real
      {ω | ε * M ≤ |sampleCount U ω - ∑ j : U, p j|} ≤
        2 * Real.exp (-(ε ^ 2 * M) / 8) := by
  let μ := ∑ j : U, p j
  let A : Set (Fin n → Bool) := {ω | sampleCount U ω ≤ μ - ε * M}
  let B : Set (Fin n → Bool) := {ω | μ + ε * M ≤ sampleCount U ω}
  have hevent : {ω | ε * M ≤ |sampleCount U ω - μ|} = A ∪ B := by
    ext ω
    change ε * M ≤ |sampleCount U ω - μ| ↔
      sampleCount U ω ≤ μ - ε * M ∨ μ + ε * M ≤ sampleCount U ω
    constructor
    · intro h
      by_cases hsign : 0 ≤ sampleCount U ω - μ
      · rw [abs_of_nonneg hsign] at h
        exact Or.inr (by linarith)
      · rw [abs_of_neg (lt_of_not_ge hsign)] at h
        exact Or.inl (by linarith)
    · rintro (h | h)
      · have habs := neg_le_abs (sampleCount U ω - μ)
        linarith
      · have habs := le_abs_self (sampleCount U ω - μ)
        linarith
  have htails := sample_count_tails p U M ε hp₀ hp₁ hM hε₀ hε₁
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun j _ => hp₀ j.val)
  have hM₀ : 0 ≤ M := hμ.trans hM
  have hcompare : Real.exp (-(ε ^ 2 * M) / 4) ≤ Real.exp (-(ε ^ 2 * M) / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sq_nonneg ε) hM₀]
  rw [hevent]
  calc
    (bernoulliCubeMeasure p hp₀ hp₁).real (A ∪ B) ≤
        (bernoulliCubeMeasure p hp₀ hp₁).real A +
          (bernoulliCubeMeasure p hp₀ hp₁).real B := MeasureTheory.measureReal_union_le _ _
    _ ≤ Real.exp (-(ε ^ 2 * M) / 4) + Real.exp (-(ε ^ 2 * M) / 8) :=
      add_le_add htails.2 htails.1
    _ ≤ 2 * Real.exp (-(ε ^ 2 * M) / 8) := by linarith

end Erdos911
