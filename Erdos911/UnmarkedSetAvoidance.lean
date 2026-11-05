import Erdos911.ConditionalMarkBudget

open MeasureTheory

namespace Erdos911

theorem subtype_filter_card_le {I : Type*} [Fintype I] (C : Finset I)
    (P : I → Prop) [DecidablePred P] :
    ((Finset.univ : Finset C).filter (fun i => P i.val)).card ≤
      ((Finset.univ : Finset I).filter P).card := by
  classical
  let S := (Finset.univ : Finset C).filter (fun i => P i.val)
  have hsub : S.image Subtype.val ⊆ (Finset.univ : Finset I).filter P := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  calc
    S.card = (S.image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- A finite family of sufficiently large sets with bounded incidence
admits a marking that hits every set, with conditional mark control. -/
theorem unmarked_sets_avoidance {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I]
    (S : I → Finset E) (b N : ℕ) (hsize : ∀ i, b ≤ (S i).card)
    (hcount : ∀ e, (Finset.univ.filter (fun i => e ∈ S i)).card ≤ N)
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * b / 2) ≤ 1 / 2)
    (hincidence : (N : ℝ) * Real.exp (-p * b / 2) ≤ q) :
    0 < (bitProductMeasure E p hp₀ hp₁).real (avoidAll (fun i => fixedBits (S i) false)) ∧
      ∀ T : Finset E, (bitProductMeasure E p hp₀ hp₁).real
        (fixedBits T true ∩ avoidAll (fun i => fixedBits (S i) false)) /
          (bitProductMeasure E p hp₀ hp₁).real (avoidAll (fun i => fixedBits (S i) false)) ≤
            p ^ T.card * Real.exp (2 * (q * T.card)) := by
  classical
  let x := Real.exp (-p * b / 2)
  have hweights : ∀ e : E, ∑ i ∈ Finset.univ.filter (fun i => e ∈ S i), x ≤ q := by
    intro e
    have hreal : ((Finset.univ.filter (fun i => e ∈ S i)).card : ℝ) ≤ N := by
      exact_mod_cast hcount e
    simpa only [Finset.sum_const, nsmul_eq_mul, x] using
      (mul_le_mul_of_nonneg_right hreal (Real.exp_pos _).le).trans hincidence
  have hprob : ∀ i, (bitProductMeasure E p hp₀ hp₁).real (fixedBits (S i) false) ≤
      x * Real.exp (-2 * (q * (S i).card)) := by
    intro i
    rw [bitProductMeasure_fixedBits]
    change (1 - p) ^ (S i).card ≤ _
    have hweight : Real.exp (-p * (S i).card / 2) ≤ x := by
      apply Real.exp_le_exp.mpr
      have hb : (b : ℝ) ≤ (S i).card := by exact_mod_cast hsize i
      nlinarith
    exact (unmarked_probability_lll_bound p q hp₁ hq (S i).card).trans
      (mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le)
  have h := coordinate_lll_from_exp_bounds_fintype
    (fun _ : E => bernoulliMarginal p hp₀ hp₁) (fun i => fixedBits (S i) false) S
    (fun i => fixedBits_depends (S i) false) (fun _ => x) q
    (fun _ => (Real.exp_pos _).le) (fun _ => hhalf) hweights hprob
  refine ⟨h.1, ?_⟩
  intro T
  have ht := h.2 (fixedBits T true) T (fixedBits_depends T true)
  change (bitProductMeasure E p hp₀ hp₁).real
      (fixedBits T true ∩ avoidAll (fun i => fixedBits (S i) false)) /
      (bitProductMeasure E p hp₀ hp₁).real (avoidAll (fun i => fixedBits (S i) false)) ≤
    (bitProductMeasure E p hp₀ hp₁).real (fixedBits T true) *
      Real.exp (2 * (q * T.card)) at ht
  simpa only [bitProductMeasure_fixedBits, bernoulliWeight, ite_true] using ht

theorem exists_marks_meeting_sets {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I]
    (S : I → Finset E) (b N : ℕ) (hsize : ∀ i, b ≤ (S i).card)
    (hcount : ∀ e, (Finset.univ.filter (fun i => e ∈ S i)).card ≤ N)
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * b / 2) ≤ 1 / 2)
    (hincidence : (N : ℝ) * Real.exp (-p * b / 2) ≤ q)
    (hfactor : Real.exp (2 * q) ≤ 2) :
    ∃ ω : E → Bool, ((Finset.univ.filter (fun e => ω e = true)).card : ℝ) ≤
      2 * p * Fintype.card E ∧ ∀ i, ∃ e ∈ S i, ω e = true := by
  classical
  obtain ⟨hpositive, hconditional⟩ := unmarked_sets_avoidance S b N hsize hcount p q
    hp₀ hp₁ hq hhalf hincidence
  have hmark : ∀ e : E, (bitProductMeasure E p hp₀ hp₁).real
      (fixedBits {e} true ∩ avoidAll (fun i => fixedBits (S i) false)) /
        (bitProductMeasure E p hp₀ hp₁).real (avoidAll (fun i => fixedBits (S i) false)) ≤ 2 * p := by
    intro e
    have h := hconditional {e}
    simp only [Finset.card_singleton, pow_one, Nat.cast_one, mul_one] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hfactor hp₀])
  obtain ⟨ω, hω, hcost⟩ := exists_conditional_mark_budget p hp₀ hp₁
    (avoidAll (fun i => fixedBits (S i) false)) hpositive (fun _ => 1) (by simp) (2 * p) hmark
  refine ⟨ω, ?_, ?_⟩
  · have hcard : ((Finset.univ.filter (fun e => ω e = true)).card : ℝ) =
        ∑ e, if ω e = true then (1 : ℝ) else 0 := by
      exact_mod_cast Finset.card_filter (fun e => ω e = true) (Finset.univ : Finset E)
    rw [hcard]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hcost
  · intro i
    by_contra hn
    apply hω i
    intro e he
    have hne : ω e ≠ true := fun h => hn ⟨e, he, h⟩
    cases hvalue : ω e <;> simp_all

theorem log_bound_mark_parameters (b N : ℕ) (hN : 0 < N)
    (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * N / p) ≤ p * b / 2) :
    Real.exp (-p * b / 2) ≤ 1 / 2 ∧
      (N : ℝ) * Real.exp (-p * b / 2) ≤ p / 8 ∧ Real.exp (2 * (p / 8)) ≤ 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hexp : Real.exp (-p * b / 2) ≤ p / (8 * N) := by
    calc
      _ ≤ Real.exp (-Real.log (8 * N / p)) := Real.exp_le_exp.mpr (by linarith)
      _ = p / (8 * N) := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  have hincidence : (N : ℝ) * Real.exp (-p * b / 2) ≤ p / 8 := by
    have h := mul_le_mul_of_nonneg_left hexp hNreal.le
    have heq : (N : ℝ) * (p / (8 * N)) = p / 8 := by field_simp
    simpa only [heq] using h
  have hhalf : Real.exp (-p * b / 2) ≤ 1 / 2 := by
    have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h := mul_le_mul_of_nonneg_right hNge (Real.exp_pos (-p * b / 2)).le
    nlinarith
  have hfactor : Real.exp (2 * (p / 8)) ≤ 2 := by
    have hehalf := Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    norm_num at hehalf
    exact (Real.exp_le_exp.mpr (by linarith : 2 * (p / 8) ≤ (1 / 2 : ℝ))).trans hehalf
  exact ⟨hhalf, hincidence, hfactor⟩

/-- The logarithmic condition preserves the conditional probability of
every specified marked set, as well as positive avoidance probability. -/
theorem unmarked_sets_avoidance_of_log_bound {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I]
    (S : I → Finset E) (b N : ℕ) (hN : 0 < N) (hsize : ∀ i, b ≤ (S i).card)
    (hcount : ∀ e, (Finset.univ.filter (fun i => e ∈ S i)).card ≤ N)
    (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * N / p) ≤ p * b / 2) :
    0 < (bitProductMeasure E p hp₀.le hp₁).real (avoidAll (fun i => fixedBits (S i) false)) ∧
      ∀ T : Finset E, (bitProductMeasure E p hp₀.le hp₁).real
        (fixedBits T true ∩ avoidAll (fun i => fixedBits (S i) false)) /
          (bitProductMeasure E p hp₀.le hp₁).real (avoidAll (fun i => fixedBits (S i) false)) ≤
            (p * Real.exp (p / 4)) ^ T.card := by
  obtain ⟨hhalf, hincidence, _⟩ := log_bound_mark_parameters b N hN p hp₀ hp₁ hlog
  obtain ⟨hpositive, hconditional⟩ := unmarked_sets_avoidance S b N hsize hcount
    p (p / 8) hp₀.le hp₁ (by linarith) hhalf hincidence
  refine ⟨hpositive, ?_⟩
  intro T
  have h := hconditional T
  rw [marked_probability_exponential_factor] at h
  have heq : 2 * (p / 8) = p / 4 := by ring
  simpa only [heq] using h

/-- A single logarithmic inequality supplies all local-lemma parameters. -/
theorem exists_marks_meeting_sets_of_log_bound {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I]
    (S : I → Finset E) (b N : ℕ) (hN : 0 < N) (hsize : ∀ i, b ≤ (S i).card)
    (hcount : ∀ e, (Finset.univ.filter (fun i => e ∈ S i)).card ≤ N)
    (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * N / p) ≤ p * b / 2) :
    ∃ ω : E → Bool, ((Finset.univ.filter (fun e => ω e = true)).card : ℝ) ≤
      2 * p * Fintype.card E ∧ ∀ i, ∃ e ∈ S i, ω e = true := by
  obtain ⟨hhalf, hincidence, hfactor⟩ := log_bound_mark_parameters b N hN p hp₀ hp₁ hlog
  exact exists_marks_meeting_sets S b N hsize hcount p (p / 8) hp₀.le hp₁
    (by linarith) hhalf hincidence hfactor

end Erdos911
