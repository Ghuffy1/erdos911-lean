import Erdos911.ExponentialEventMarking

namespace Erdos911

/-- One logarithmic bound supplies the coordinate weight, event size,
and conditional-factor conditions for the exponential-event local lemma. -/
theorem exponential_event_log_parameters (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (a : ℝ) (ha : 1 ≤ a) (hlog : Real.log (8 * (N : ℝ) * b) ≤ a / 2) :
    0 ≤ 1 / (8 * (b : ℝ)) ∧ Real.exp (-a / 2) ≤ 1 / 2 ∧
      (N : ℝ) * Real.exp (-a / 2) ≤ 1 / (8 * (b : ℝ)) ∧
      4 * (1 / (8 * (b : ℝ))) * b ≤ a ∧ Real.exp (2 * (1 / (8 * (b : ℝ)))) ≤ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbge : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hexp : Real.exp (-a / 2) ≤ 1 / (8 * (N : ℝ) * b) := by
    calc
      _ ≤ Real.exp (-Real.log (8 * (N : ℝ) * b)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hincidence : (N : ℝ) * Real.exp (-a / 2) ≤ 1 / (8 * (b : ℝ)) := by
    apply (mul_le_mul_of_nonneg_left hexp hNR.le).trans_eq
    field_simp
  have hsmall : 1 / (8 * (b : ℝ)) ≤ 1 / 8 := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hhalf : Real.exp (-a / 2) ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hNge (Real.exp_pos (-a / 2)).le
    nlinarith
  have hsize : 4 * (1 / (8 * (b : ℝ))) * b = 1 / 2 := by field_simp; ring
  have hfactor : Real.exp (2 * (1 / (8 * (b : ℝ)))) ≤ 2 := by
    have hbound := Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    norm_num at hbound
    exact (Real.exp_le_exp.mpr (by linarith : 2 * (1 / (8 * (b : ℝ))) ≤ 1 / 2)).trans hbound
  exact ⟨by positivity, hhalf, hincidence, by rw [hsize]; linarith, hfactor⟩

theorem exists_exponential_event_marks_of_log_bound {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I]
    (A : I → Set (E → Bool)) (S : I → Finset E)
    (hdep : ∀ i, DependsOnlyOn (A i) (S i)) (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (hsize : ∀ i, (S i).card ≤ b)
    (hcount : ∀ e, (Finset.univ.filter (fun i => e ∈ S i)).card ≤ N)
    (p a : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ha : 1 ≤ a)
    (hprob : ∀ i, (bitProductMeasure E p hp₀ hp₁).real (A i) ≤ Real.exp (-a))
    (hlog : Real.log (8 * (N : ℝ) * b) ≤ a / 2)
    (cost : E → ℝ) (hcost : ∀ e, 0 ≤ cost e) :
    ∃ marks : E → Bool, (∀ i, marks ∉ A i) ∧
      (∑ e, if marks e = true then cost e else 0) ≤ (2 * p) * ∑ e, cost e := by
  obtain ⟨hν, hhalf, hincidence, hsizegap, hfactor⟩ :=
    exponential_event_log_parameters N b hN hb a ha hlog
  exact exists_exponential_event_marks A S hdep N b hsize hcount p a (1 / (8 * b))
    hp₀ hp₁ hν hprob hhalf hincidence hsizegap hfactor cost hcost

end Erdos911
