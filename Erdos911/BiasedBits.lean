import Erdos911.CubeMeasure
import Erdos911.ProductCoordinates

open MeasureTheory

namespace Erdos911

noncomputable def bitProductMeasure (E : Type*) [Fintype E]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : Measure (E → Bool) :=
  Measure.pi (fun _ => bernoulliMarginal p hp₀ hp₁)

instance bitProductMeasure_isProbabilityMeasure (E : Type*) [Fintype E]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsProbabilityMeasure (bitProductMeasure E p hp₀ hp₁) := by
  unfold bitProductMeasure
  infer_instance

def fixedBits {E : Type*} (S : Finset E) (b : Bool) : Set (E → Bool) :=
  {ω | ∀ e ∈ S, ω e = b}

theorem fixedBits_depends {E : Type*} (S : Finset E) (b : Bool) :
    DependsOnlyOn (fixedBits S b) S := by
  intro ω ω' heq hω e he
  rw [← heq e he]
  exact hω e he

theorem bitProductMeasure_fixedBits {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (S : Finset E) (b : Bool) :
    (bitProductMeasure E p hp₀ hp₁).real (fixedBits S b) = (bernoulliWeight p b) ^ S.card := by
  classical
  have hset : fixedBits S b =
      Set.univ.pi (fun e => if e ∈ S then ({b} : Set Bool) else Set.univ) := by
    ext ω
    simp only [fixedBits, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h e
      by_cases he : e ∈ S
      · simpa only [ite_eq_left he, Set.mem_singleton_iff] using h e he
      · simp only [ite_eq_right he, Set.mem_univ]
    · intro h e he
      simpa only [ite_eq_left he, Set.mem_singleton_iff] using h e
  calc
    (bitProductMeasure E p hp₀ hp₁).real (fixedBits S b) =
        ∏ e : E, (bernoulliMarginal p hp₀ hp₁).real
          (if e ∈ S then {b} else Set.univ) := by
      simp only [Measure.real, bitProductMeasure, hset, Measure.pi_pi, ENNReal.toReal_prod]
    _ = ∏ e : E, if e ∈ S then bernoulliWeight p b else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ S
      · simp only [ite_eq_left he, bernoulliMarginal_real_singleton]
      · simp only [ite_eq_right he, probReal_univ]
    _ = (bernoulliWeight p b) ^ S.card := by
      rw [Finset.prod_ite_mem_eq, Finset.prod_const]

theorem unmarked_probability_exp_bound (p : ℝ) (hp₁ : p ≤ 1) (a : ℕ) :
    (1 - p) ^ a ≤ Real.exp (-p * a) := by
  have hbase : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc
    (1 - p) ^ a ≤ Real.exp (-p) ^ a := pow_le_pow_left₀ (by linarith) hbase a
    _ = Real.exp (-p * a) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem unmarked_probability_lll_bound (p q : ℝ) (hp₁ : p ≤ 1)
    (hq : 4 * q ≤ p) (a : ℕ) :
    (1 - p) ^ a ≤ Real.exp (-p * a / 2) * Real.exp (-2 * (q * a)) := by
  apply (unmarked_probability_exp_bound p hp₁ a).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (Nat.cast_nonneg (α := ℝ) a)]

theorem marked_probability_exponential_factor (p q : ℝ) (a : ℕ) :
    p ^ a * Real.exp (2 * (q * a)) = (p * Real.exp (2 * q)) ^ a := by
  rw [mul_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end Erdos911
