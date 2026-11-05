import Erdos911.SampleConcentration

open MeasureTheory

namespace Erdos911

theorem exists_le_cubeMean {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (f : (Fin n → Bool) → ℝ) : ∃ ω, f ω ≤ cubeMean p f := by
  by_contra hn
  have hstrict : ∀ ω, cubeMean p f < f ω := fun ω =>
    lt_of_not_ge (fun h => hn ⟨ω, h⟩)
  have hpositive := cubeMean_pos p hp₀ hp₁
    (fun ω => sub_pos.mpr (hstrict ω))
  rw [cubeMean_sub, cubeMean_const] at hpositive
  linarith

noncomputable def repairCount {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Set (Fin n → Bool)) (ω : Fin n → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => ω ∈ A i)).card

theorem repairCount_real {n : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Set (Fin n → Bool)) (ω : Fin n → Bool) :
    (repairCount A ω : ℝ) = ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  simp [repairCount, Set.indicator]

theorem cubeMean_repairCount {n : ℕ} {ι : Type*} [Fintype ι]
    (p : Fin n → ℝ) (A : ι → Set (Fin n → Bool)) :
    cubeMean p (fun ω => (repairCount A ω : ℝ)) = ∑ i, cubeProbability p (A i) := by
  simp_rw [repairCount_real]
  rw [cubeMean_sum]
  rfl

theorem cubeMean_sampleCount {n : ℕ} (p : Fin n → ℝ) (U : Finset (Fin n)) :
    cubeMean p (sampleCount U) = ∑ j ∈ U, p j := by
  unfold sampleCount
  rw [cubeMean_sum]
  simp_rw [cubeMean_coordinate]
  exact Finset.sum_coe_sort U p

/-- Choose a sample whose size plus the number of local repairs is at most
the total expected cost. No independence among the repair events is needed. -/
theorem exists_sample_repair_budget {n : ℕ} {ι : Type*} [Fintype ι]
    (p : Fin n → ℝ) (A : ι → Set (Fin n → Bool)) (ε : ι → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hA : ∀ i, cubeProbability p (A i) ≤ ε i) :
    ∃ ω, sampleCount Finset.univ ω + (repairCount A ω : ℝ) ≤
      (∑ j, p j) + ∑ i, ε i := by
  obtain ⟨ω, hω⟩ := exists_le_cubeMean p hp₀ hp₁
    (fun ω => sampleCount Finset.univ ω + (repairCount A ω : ℝ))
  refine ⟨ω, hω.trans ?_⟩
  rw [cubeMean_add, cubeMean_sampleCount, cubeMean_repairCount]
  exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ => hA i))

theorem empty_sample_probability {n : ℕ} (p : Fin n → ℝ) (U : Finset (Fin n))
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) :
    cubeProbability p {ω | ∀ j ∈ U, ω j = false} = ∏ j ∈ U, (1 - p j) := by
  classical
  have hevent : {ω : Fin n → Bool | ∀ j ∈ U, ω j = false} =
      Set.univ.pi (fun j => if j ∈ U then ({false} : Set Bool) else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h j
      by_cases hj : j ∈ U
      · simpa only [ite_eq_left hj, Set.mem_singleton_iff] using h j hj
      · simp [hj]
    · intro h j hj
      simpa only [ite_eq_left hj, Set.mem_singleton_iff] using h j
  rw [cubeProbability_eq_measureReal p hp₀ hp₁, hevent]
  unfold bernoulliCubeMeasure
  rw [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  calc
    (∏ j, ((bernoulliMarginal (p j) (hp₀ j) (hp₁ j))
        (if j ∈ U then {false} else Set.univ)).toReal) =
        ∏ j, if j ∈ U then (1 - p j) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ U
      · simp only [ite_eq_left hj]
        exact bernoulliMarginal_real_singleton (p j) (hp₀ j) (hp₁ j) false
      · simp only [ite_eq_right hj]
        exact probReal_univ
    _ = ∏ j ∈ U, (1 - p j) := by rw [← Finset.prod_filter]; simp

theorem empty_sample_probability_le {n : ℕ} (p : ℝ) (U : Finset (Fin n))
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    cubeProbability (fun _ => p) {ω | ∀ j ∈ U, ω j = false} ≤
      Real.exp (-p * U.card) := by
  rw [empty_sample_probability (fun _ => p) U (fun _ => hp₀) (fun _ => hp₁),
    Finset.prod_const]
  calc
    (1 - p) ^ U.card ≤ Real.exp (-p) ^ U.card := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr hp₁)
      linarith [Real.add_one_le_exp (-p)]
    _ = Real.exp (-p * U.card) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem sampleCount_eq_card {n : ℕ} (U : Finset (Fin n)) (ω : Fin n → Bool) :
    sampleCount U ω = ((U.filter (fun j => ω j = true)).card : ℝ) := by
  unfold sampleCount
  rw [Finset.sum_coe_sort U (fun j => coordinateIndicator j ω)]
  simp [coordinateIndicator]

end Erdos911
