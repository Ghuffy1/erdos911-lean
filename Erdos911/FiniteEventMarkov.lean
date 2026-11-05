import Erdos911.ConditionalMarkBudget

open MeasureTheory

namespace Erdos911

noncomputable def eventHitSet {Ω I : Type*} (A : I → Set Ω) (S : Finset I) (ω : Ω) : Finset I := by
  classical
  exact S.filter (fun i => ω ∈ A i)

theorem mem_eventHitSet {Ω I : Type*} (A : I → Set Ω) (S : Finset I) (ω : Ω) (i : I) :
    i ∈ eventHitSet A S ω ↔ i ∈ S ∧ ω ∈ A i := by
  classical
  exact Finset.mem_filter

theorem eventHitSet_eq_of_agreement {ι I : Type*} {β : ι → Type*}
    (A : I → Set (∀ i, β i)) (S : Finset I) (T : Finset ι)
    (hA : ∀ i ∈ S, DependsOnlyOn (A i) T)
    (ω ω' : ∀ i, β i) (heq : ∀ e ∈ T, ω e = ω' e) :
    eventHitSet A S ω = eventHitSet A S ω' := by
  classical
  ext i
  simp only [mem_eventHitSet]
  constructor
  · rintro ⟨hi, hω⟩
    exact ⟨hi, hA i hi ω ω' heq hω⟩
  · rintro ⟨hi, hω⟩
    exact ⟨hi, hA i hi ω' ω (fun e he => (heq e he).symm) hω⟩

/-- A finite counting form of Markov's inequality, valid for arbitrary
dependence among the events being counted. -/
theorem finite_event_count_markov {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq I] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω) (S : Finset I)
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t ≤ ((eventHitSet A S ω).card : ℝ)} ≤
      (∑ i ∈ S, μ.real (A i)) / t := by
  classical
  let B : Set Ω := {ω | t ≤ ((eventHitSet A S ω).card : ℝ)}
  have hpoint (ω : Ω) : (if ω ∈ B then t else 0) ≤
      ∑ i ∈ S, if ω ∈ A i then (1 : ℝ) else 0 := by
    have hcount : (∑ i ∈ S, if ω ∈ A i then (1 : ℝ) else 0) =
        ((S.filter (fun i => ω ∈ A i)).card : ℝ) := by simp
    rw [hcount]
    by_cases hω : ω ∈ B
    · simp only [hω, ite_true]
      exact hω
    · simp only [hω, ite_false]
      positivity
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ (Finset.univ : Finset Ω)) =>
    mul_le_mul_of_nonneg_left (hpoint ω) (show 0 ≤ μ.real {ω} from measureReal_nonneg))
  have hleft : (∑ ω : Ω, μ.real {ω} * (if ω ∈ B then t else 0)) = μ.real B * t := by
    calc
      _ = (∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ B), μ.real {ω}) * t := by
        rw [Finset.sum_mul, Finset.sum_filter]
        exact Finset.sum_congr rfl (fun ω _ => by split_ifs <;> simp_all)
      _ = μ.real B * t := by
        rw [sum_measureReal_singleton]
        congr 2
        ext ω
        simp
  have hright : (∑ ω : Ω, μ.real {ω} * (∑ i ∈ S, if ω ∈ A i then (1 : ℝ) else 0)) =
      ∑ i ∈ S, μ.real (A i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (∑ ω : Ω, μ.real {ω} * (if ω ∈ A i then (1 : ℝ) else 0)) =
          ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ A i), μ.real {ω} := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun ω _ => by split_ifs <;> simp_all)
      _ = μ.real (A i) := by
        rw [sum_measureReal_singleton]
        congr 1
        ext ω
        simp
  rw [hleft, hright] at hsum
  exact (le_div_iff₀ ht).mpr hsum

end Erdos911
