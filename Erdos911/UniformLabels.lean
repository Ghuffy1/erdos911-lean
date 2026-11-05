import Erdos911.CollisionCounting
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory

namespace Erdos911

noncomputable def uniformLabelMeasure (V A : Type*) [Fintype V] [Fintype A] [Nonempty A]
    [MeasurableSpace A] : Measure (V → A) :=
  Measure.pi (fun _ : V => (PMF.uniformOfFintype A).toMeasure)

instance uniformLabelMeasure_isProbabilityMeasure (V A : Type*)
    [Fintype V] [Fintype A] [Nonempty A] [MeasurableSpace A] :
    IsProbabilityMeasure (uniformLabelMeasure V A) := by
  unfold uniformLabelMeasure
  infer_instance

theorem uniformLabelMeasure_singleton (V A : Type*) [Fintype V] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : V → A) :
    (uniformLabelMeasure V A).real {f} =
      (1 / (Fintype.card A : ℝ)) ^ Fintype.card V := by
  classical
  have hm (a : A) : ((PMF.uniformOfFintype A).toMeasure {a}).toReal =
      1 / (Fintype.card A : ℝ) := by
    rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a), PMF.uniformOfFintype_apply]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  simp only [Measure.real, uniformLabelMeasure, Measure.pi_singleton, ENNReal.toReal_prod,
    hm, Finset.prod_const, Finset.card_univ]

theorem uniformLabelMeasure_finset (V A : Type*) [Fintype V] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (S : Finset (V → A)) :
    (uniformLabelMeasure V A).real (S : Set (V → A)) =
      S.card * (1 / (Fintype.card A : ℝ)) ^ Fintype.card V := by
  classical
  rw [← sum_measureReal_singleton]
  simp only [uniformLabelMeasure_singleton, Finset.sum_const, nsmul_eq_mul]

theorem uniformLabelMeasure_many_collisions (A : Type*) [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (n r : ℕ) (hr : r ≤ n) :
    (uniformLabelMeasure (Fin n) A).real (manyCollisionLabels A n r : Set (Fin n → A)) ≤
      (2 : ℝ) ^ n * ((n : ℝ) / Fintype.card A) ^ r := by
  classical
  rw [uniformLabelMeasure_finset, Fintype.card_fin]
  have hcard : ((manyCollisionLabels A n r).card : ℝ) ≤
      (2 : ℝ) ^ n * (n : ℝ) ^ r * (Fintype.card A : ℝ) ^ (n - r) := by
    exact_mod_cast manyCollisionLabels_card_le A n r
  have hp : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have h := mul_le_mul_of_nonneg_right hcard
    (show (0 : ℝ) ≤ (1 / (Fintype.card A : ℝ)) ^ n by positivity)
  apply h.trans_eq
  have hpow : (Fintype.card A : ℝ) ^ n =
      (Fintype.card A : ℝ) ^ (n - r) * (Fintype.card A : ℝ) ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [one_div, inv_pow, hpow, mul_inv_rev, div_pow]
  field_simp

end Erdos911
