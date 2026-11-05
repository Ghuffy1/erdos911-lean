import Erdos911.ConditionalMarkBudget

open MeasureTheory

namespace Erdos911

def patternBits {E : Type*} (S : Finset E) (b : E → Bool) : Set (E → Bool) :=
  {ω | ∀ e ∈ S, ω e = b e}

theorem bitProductMeasure_patternBits {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (S : Finset E) (b : E → Bool) :
    (bitProductMeasure E p hp₀ hp₁).real (patternBits S b) =
      ∏ e ∈ S, bernoulliWeight p (b e) := by
  classical
  have hset : patternBits S b =
      Set.univ.pi (fun e => if e ∈ S then ({b e} : Set Bool) else Set.univ) := by
    ext ω
    simp only [patternBits, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h e
      by_cases he : e ∈ S
      · simpa only [ite_eq_left he, Set.mem_singleton_iff] using h e he
      · simp only [ite_eq_right he, Set.mem_univ]
    · intro h e he
      simpa only [ite_eq_left he, Set.mem_singleton_iff] using h e
  calc
    _ = ∏ e : E, (bernoulliMarginal p hp₀ hp₁).real
        (if e ∈ S then {b e} else Set.univ) := by
      simp only [Measure.real, bitProductMeasure, hset, Measure.pi_pi, ENNReal.toReal_prod]
    _ = ∏ e : E, if e ∈ S then bernoulliWeight p (b e) else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S
      · simp only [ite_eq_left he, bernoulliMarginal_real_singleton]
      · simp only [ite_eq_right he, probReal_univ]
    _ = _ := by rw [Finset.prod_ite_mem_eq]

theorem bitProductMeasure_two_bits {E : Type*} [Fintype E] [DecidableEq E]
    (u v : E) (huv : u ≠ v) (a b : Bool) :
    (bitProductMeasure E (1 / 2) (by norm_num) (by norm_num)).real
      {ω | ω u = a ∧ ω v = b} = 1 / 4 := by
  classical
  let f : E → Bool := fun x => if x = u then a else b
  have hset : {ω : E → Bool | ω u = a ∧ ω v = b} = patternBits {u, v} f := by
    ext ω
    simp [patternBits, f, huv.symm]
  rw [hset, bitProductMeasure_patternBits]
  cases a <;> cases b <;> simp [f, huv, huv.symm, bernoulliWeight] <;> norm_num

/-- A finite family of events each having probability at least q has
an outcome satisfying at least q times the number of events. -/
theorem exists_many_binary_events {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I]
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (A : I → Set (E → Bool))
    (hprob : ∀ i, q ≤ (bitProductMeasure E p hp₀ hp₁).real (A i)) :
    ∃ (ω : E → Bool) (S : Finset I), (∀ i, i ∈ S ↔ ω ∈ A i) ∧
      q * Fintype.card I ≤ (S.card : ℝ) := by
  classical
  let μ := bitProductMeasure E p hp₀ hp₁
  obtain ⟨ω, _, hcost⟩ := exists_conditional_cost_le μ Set.univ (by simp)
    (fun i => (A i)ᶜ) (fun _ => 1) (fun _ => 1 - q) (by intro _; norm_num) (by
      intro i
      have h := measureReal_add_measureReal_compl (μ := μ) ((Set.toFinite (A i)).measurableSet)
      have hp := hprob i
      simp only [Set.inter_univ, probReal_univ, div_one]
      simp only [probReal_univ] at h
      linarith only [h, hp])
  have hcost' : (((Finset.univ : Finset I).filter (fun i => ω ∉ A i)).card : ℝ) ≤
      (1 - q) * Fintype.card I := by
    simpa only [Set.indicator, Set.mem_compl_iff, Finset.sum_boole, mul_one, one_mul,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hcost
  have hpartition : (((Finset.univ : Finset I).filter (fun i => ω ∈ A i)).card : ℝ) +
      (((Finset.univ : Finset I).filter (fun i => ω ∉ A i)).card : ℝ) = Fintype.card I := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I)) (fun i => ω ∈ A i)
  exact ⟨ω, Finset.univ.filter (fun i => ω ∈ A i), by simp, by linarith only [hcost', hpartition]⟩

end Erdos911
