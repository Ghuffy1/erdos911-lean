import Erdos911.BiasedBits

open MeasureTheory

namespace Erdos911

/-- Apply the independent choices in chronological order. -/
def runRounds {S Ω : Type*} (update : S → Ω → S) :
    {h : ℕ} → S → (Fin h → Ω) → S
  | 0, state, _ => state
  | _ + 1, state, choices => runRounds update (update state (choices 0)) (fun i => choices i.succ)

def roundWeight {Ω : Type*} (w : Ω → ℝ) {h : ℕ} (choices : Fin h → Ω) : ℝ :=
  ∏ i, w (choices i)

theorem runRounds_cons {S Ω : Type*} (update : S → Ω → S) {h : ℕ}
    (state : S) (choice : Ω) (choices : Fin h → Ω) :
    runRounds update state (Fin.cons choice choices) = runRounds update (update state choice) choices := by
  simp only [runRounds, Fin.cons_zero, Fin.cons_succ]

theorem roundWeight_cons {Ω : Type*} (w : Ω → ℝ) {h : ℕ}
    (choice : Ω) (choices : Fin h → Ω) :
    roundWeight w (Fin.cons choice choices) = w choice * roundWeight w choices := by
  simp only [roundWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem roundWeight_nonneg {Ω : Type*} (w : Ω → ℝ) (hw : ∀ choice, 0 ≤ w choice)
    {h : ℕ} (choices : Fin h → Ω) : 0 ≤ roundWeight w choices :=
  Finset.prod_nonneg (fun i _ => hw (choices i))

theorem independent_round_mean_cons {S Ω : Type*} [Fintype Ω]
    (update : S → Ω → S) (w : Ω → ℝ) (value : S → ℝ) (h : ℕ) (state : S) :
    weightedMean (fun choices : Fin (h + 1) → Ω => roundWeight w choices)
      (fun choices => value (runRounds update state choices)) =
    weightedMean w (fun choice =>
      weightedMean (fun choices : Fin h → Ω => roundWeight w choices)
        (fun choices => value (runRounds update (update state choice) choices))) := by
  unfold weightedMean
  calc
    _ = ∑ pair : Ω × (Fin h → Ω), roundWeight w (Fin.cons pair.1 pair.2) *
        value (runRounds update state (Fin.cons pair.1 pair.2)) :=
      ((Fin.consEquiv (fun _ : Fin (h + 1) => Ω)).sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [roundWeight_cons, runRounds_cons, Finset.mul_sum, mul_assoc]

/-- A lower bound for each successive progress event multiplies across
independent rounds, even when the event depends on the current state. -/
theorem independent_rounds_reach_weight {S Ω : Type*} [Fintype Ω]
    (update : S → Ω → S) (w : Ω → ℝ) (hw : ∀ choice, 0 ≤ w choice)
    (P : ℕ → Set S) (terminal : Set S) (hterminal : P 0 ⊆ terminal)
    (β : ℝ) (hβ : 0 ≤ β)
    (hstep : ∀ h state, state ∈ P (h + 1) →
      β ≤ weightedMean w (({choice | update state choice ∈ P h} : Set Ω).indicator (fun _ => 1))) :
    ∀ h state, state ∈ P h →
      β ^ h ≤ weightedMean (fun choices : Fin h → Ω => roundWeight w choices)
        (fun choices => terminal.indicator (fun _ => 1) (runRounds update state choices)) := by
  classical
  intro h
  induction h with
  | zero =>
    intro state hs
    simp [weightedMean, roundWeight, runRounds, hterminal hs]
  | succ h ih =>
    intro state hs
    rw [independent_round_mean_cons, pow_succ]
    have hmean_nonneg (choice : Ω) :
        0 ≤ weightedMean (fun choices : Fin h → Ω => roundWeight w choices)
          (fun choices => terminal.indicator (fun _ => 1) (runRounds update (update state choice) choices)) := by
      apply Finset.sum_nonneg
      intro choices _
      exact mul_nonneg (roundWeight_nonneg w hw choices) (by simp only [Set.indicator]; split_ifs <;> norm_num)
    calc
      β ^ h * β ≤ β ^ h * weightedMean w
          (({choice | update state choice ∈ P h} : Set Ω).indicator (fun _ => 1)) :=
        mul_le_mul_of_nonneg_left (hstep h state hs) (pow_nonneg hβ h)
      _ = weightedMean w (fun choice => β ^ h *
          ({choice | update state choice ∈ P h} : Set Ω).indicator (fun _ => 1) choice) :=
        (weightedMean_const_mul _ _ _).symm
      _ ≤ _ := by
        apply weightedMean_mono w hw
        intro choice
        by_cases hc : update state choice ∈ P h
        · simpa [Set.indicator, hc] using ih (update state choice) hc
        · simpa [Set.indicator, hc] using hmean_nonneg choice

theorem finite_probability_eq_weighted_mean {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) :
    μ.real A = weightedMean (fun choice => μ.real {choice}) (A.indicator (fun _ => 1)) := by
  classical
  let B := Finset.univ.filter (fun choice => choice ∈ A)
  have hB : (B : Set Ω) = A := by ext choice; simp [B]
  calc
    μ.real A = ∑ choice ∈ B, μ.real {choice} := by rw [sum_measureReal_singleton, hB]
    _ = _ := by
      unfold B weightedMean
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro choice _
      by_cases hc : choice ∈ A <;> simp [hc]

theorem independent_round_probability_eq {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : ℕ) (A : Set (Fin h → Ω)) :
    (Measure.pi (fun _ : Fin h => μ)).real A =
      weightedMean (fun choices => roundWeight (fun choice => μ.real {choice}) choices)
        (A.indicator (fun _ => 1)) := by
  rw [finite_probability_eq_weighted_mean]
  congr 1
  funext choices
  simp only [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, roundWeight]

theorem independent_rounds_reach_probability {S Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (update : S → Ω → S) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : ℕ → Set S) (terminal : Set S) (hterminal : P 0 ⊆ terminal)
    (β : ℝ) (hβ : 0 ≤ β)
    (hstep : ∀ h state, state ∈ P (h + 1) → β ≤ μ.real {choice | update state choice ∈ P h})
    (h : ℕ) (state : S) (hs : state ∈ P h) :
    β ^ h ≤ (Measure.pi (fun _ : Fin h => μ)).real {choices | runRounds update state choices ∈ terminal} := by
  classical
  rw [independent_round_probability_eq]
  have h := independent_rounds_reach_weight update (fun choice => μ.real {choice})
    (fun _ => measureReal_nonneg) P terminal hterminal β hβ
    (fun h state hs => by rw [← finite_probability_eq_weighted_mean]; exact hstep h state hs) h state hs
  exact h

end Erdos911
