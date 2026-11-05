import Erdos911.ConditionalMarkBudget

open MeasureTheory

namespace Erdos911

/-- Exponentially rare coordinate events can be avoided while preserving
the conditional marking bound used to charge the blue edges. -/
theorem exponential_events_avoidance {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I]
    (A : I → Set (E → Bool)) (S : I → Finset E)
    (hdep : ∀ i, DependsOnlyOn (A i) (S i)) (N b : ℕ)
    (hsize : ∀ i, (S i).card ≤ b)
    (hcount : ∀ e, (Finset.univ.filter (fun i => e ∈ S i)).card ≤ N)
    (p a ν : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hν : 0 ≤ ν)
    (hprob : ∀ i, (bitProductMeasure E p hp₀ hp₁).real (A i) ≤ Real.exp (-a))
    (hhalf : Real.exp (-a / 2) ≤ 1 / 2)
    (hincidence : (N : ℝ) * Real.exp (-a / 2) ≤ ν)
    (hsizegap : 4 * ν * b ≤ a) :
    0 < (bitProductMeasure E p hp₀ hp₁).real (avoidAll A) ∧
      ∀ T : Finset E, (bitProductMeasure E p hp₀ hp₁).real
        (fixedBits T true ∩ avoidAll A) / (bitProductMeasure E p hp₀ hp₁).real (avoidAll A) ≤
          p ^ T.card * Real.exp (2 * (ν * T.card)) := by
  classical
  let x := Real.exp (-a / 2)
  have hweights : ∀ e : E, ∑ i ∈ Finset.univ.filter (fun i => e ∈ S i), x ≤ ν := by
    intro e
    have hc : ((Finset.univ.filter (fun i => e ∈ S i)).card : ℝ) ≤ N := by
      exact_mod_cast hcount e
    simpa only [Finset.sum_const, nsmul_eq_mul, x] using
      (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans hincidence
  have hprob' : ∀ i, (bitProductMeasure E p hp₀ hp₁).real (A i) ≤
      x * Real.exp (-2 * (ν * (S i).card)) := by
    intro i
    apply (hprob i).trans
    dsimp only [x]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hb : ((S i).card : ℝ) ≤ b := by exact_mod_cast hsize i
    have hscaled := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4 * ν by positivity)
    linarith
  have h := coordinate_lll_from_exp_bounds_fintype
    (fun _ : E => bernoulliMarginal p hp₀ hp₁) A S hdep (fun _ => x) ν
    (fun _ => (Real.exp_pos _).le) (fun _ => hhalf) hweights hprob'
  refine ⟨h.1, ?_⟩
  intro T
  have ht := h.2 (fixedBits T true) T (fixedBits_depends T true)
  change (bitProductMeasure E p hp₀ hp₁).real (fixedBits T true ∩ avoidAll A) /
    (bitProductMeasure E p hp₀ hp₁).real (avoidAll A) ≤
      (bitProductMeasure E p hp₀ hp₁).real (fixedBits T true) * Real.exp (2 * (ν * T.card)) at ht
  simpa only [bitProductMeasure_fixedBits, bernoulliWeight, ite_true] using ht

theorem exists_exponential_event_marks {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I]
    (A : I → Set (E → Bool)) (S : I → Finset E)
    (hdep : ∀ i, DependsOnlyOn (A i) (S i)) (N b : ℕ)
    (hsize : ∀ i, (S i).card ≤ b)
    (hcount : ∀ e, (Finset.univ.filter (fun i => e ∈ S i)).card ≤ N)
    (p a ν : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hν : 0 ≤ ν)
    (hprob : ∀ i, (bitProductMeasure E p hp₀ hp₁).real (A i) ≤ Real.exp (-a))
    (hhalf : Real.exp (-a / 2) ≤ 1 / 2)
    (hincidence : (N : ℝ) * Real.exp (-a / 2) ≤ ν)
    (hsizegap : 4 * ν * b ≤ a) (hfactor : Real.exp (2 * ν) ≤ 2)
    (cost : E → ℝ) (hcost : ∀ e, 0 ≤ cost e) :
    ∃ marks : E → Bool, (∀ i, marks ∉ A i) ∧
      (∑ e, if marks e = true then cost e else 0) ≤ (2 * p) * ∑ e, cost e := by
  classical
  obtain ⟨hpositive, hconditional⟩ := exponential_events_avoidance A S hdep N b hsize hcount
    p a ν hp₀ hp₁ hν hprob hhalf hincidence hsizegap
  have hmark : ∀ e : E, (bitProductMeasure E p hp₀ hp₁).real
      (fixedBits {e} true ∩ avoidAll A) / (bitProductMeasure E p hp₀ hp₁).real (avoidAll A) ≤
        2 * p := by
    intro e
    have h := hconditional {e}
    simp only [Finset.card_singleton, pow_one, Nat.cast_one, mul_one] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hfactor hp₀])
  obtain ⟨marks, hmarks, hbudget⟩ := exists_conditional_mark_budget p hp₀ hp₁
    (avoidAll A) hpositive cost hcost (2 * p) hmark
  exact ⟨marks, hmarks, hbudget⟩

end Erdos911
