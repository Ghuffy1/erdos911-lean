import Erdos911.External.LocalLemma
import Mathlib.Algebra.BigOperators.Field

open MeasureTheory ProbabilityTheory

namespace Erdos911

/-- The local-lemma lower bound is positive for every finite collection of
weights strictly below one. -/
theorem lll_avoid_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (Γ : SimpleGraph (Fin n)) [DecidableRel Γ.Adj]
    (hΓ : LocalLemma.IsDependencyGraph μ A Γ) (x : Fin n → ℝ)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j)) :
    0 < μ.real (LocalLemma.avoid A Finset.univ) := by
  have hpos : 0 < ∏ i : Fin n, (1 - x i) :=
    Finset.prod_pos fun i _ => sub_pos.mpr (hx₁ i)
  have hbound := LocalLemma.lll μ A hA Γ hΓ x hx₀ hx₁ hP
  exact hpos.trans_le (by simpa [LocalLemma.avoid] using hbound)

/-- Conditional local lemma in a product form. The extra event is independent
of all bad events outside `J` jointly, as expressed by generated sigma-algebras. -/
theorem conditional_lll_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (Γ : SimpleGraph (Fin n)) [DecidableRel Γ.Adj]
    (hΓ : LocalLemma.IsDependencyGraph μ A Γ) (x : Fin n → ℝ)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j))
    (B : Set Ω) (J : Finset (Fin n))
    (hBI : Indep (MeasurableSpace.generateFrom {B})
      (MeasurableSpace.generateFrom {s | ∃ j, j ∉ J ∧ s = A j}) μ) :
    (∏ j ∈ J, (1 - x j)) * μ.real (B ∩ LocalLemma.avoid A Finset.univ) ≤
      μ.real B * μ.real (LocalLemma.avoid A Finset.univ) := by
  have hmeasB : MeasurableSet[MeasurableSpace.generateFrom {B}] B :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
  have hmeasN : MeasurableSet[MeasurableSpace.generateFrom
      {s | ∃ j, j ∉ J ∧ s = A j}] (LocalLemma.avoid A (Finset.univ \ J)) := by
    apply Finset.measurableSet_biInter
    intro j hj
    have hjgen : MeasurableSet[MeasurableSpace.generateFrom
        {s | ∃ k, k ∉ J ∧ s = A k}] (A j) :=
      MeasurableSpace.measurableSet_generateFrom
        ⟨j, (Finset.mem_sdiff.mp hj).2, rfl⟩
    exact hjgen.compl
  have hind : μ.real (B ∩ LocalLemma.avoid A (Finset.univ \ J)) =
      μ.real B * μ.real (LocalLemma.avoid A (Finset.univ \ J)) := by
    have hind' := (Indep_iff _ _ μ).mp hBI B
      (LocalLemma.avoid A (Finset.univ \ J)) hmeasB hmeasN
    simp only [Measure.real, hind', ENNReal.toReal_mul]
  have hmono : μ.real (B ∩ LocalLemma.avoid A Finset.univ) ≤
      μ.real (B ∩ LocalLemma.avoid A (Finset.univ \ J)) :=
    measureReal_mono (fun ω hω =>
      ⟨hω.1, LocalLemma.avoid_anti A Finset.sdiff_subset hω.2⟩)
  have hchain := LocalLemma.lll_chain μ A hA x hx₁ Finset.univ
    (fun S _ => LocalLemma.lll_cond μ A hA Γ hΓ x hx₀ hx₁ hP S)
    J (Finset.subset_univ J)
  have hprod : 0 ≤ ∏ j ∈ J, (1 - x j) :=
    Finset.prod_nonneg fun j _ => (sub_pos.mpr (hx₁ j)).le
  calc
    (∏ j ∈ J, (1 - x j)) * μ.real (B ∩ LocalLemma.avoid A Finset.univ) ≤
        (∏ j ∈ J, (1 - x j)) *
          (μ.real B * μ.real (LocalLemma.avoid A (Finset.univ \ J))) := by
      exact mul_le_mul_of_nonneg_left (hmono.trans_eq hind) hprod
    _ = μ.real B * ((∏ j ∈ J, (1 - x j)) *
        μ.real (LocalLemma.avoid A (Finset.univ \ J))) := by ring
    _ ≤ μ.real B * μ.real (LocalLemma.avoid A Finset.univ) :=
      mul_le_mul_of_nonneg_left hchain measureReal_nonneg

/-- The corresponding upper bound on a conditional probability. -/
theorem conditional_lll_ratio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (Γ : SimpleGraph (Fin n)) [DecidableRel Γ.Adj]
    (hΓ : LocalLemma.IsDependencyGraph μ A Γ) (x : Fin n → ℝ)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j))
    (B : Set Ω) (J : Finset (Fin n))
    (hBI : Indep (MeasurableSpace.generateFrom {B})
      (MeasurableSpace.generateFrom {s | ∃ j, j ∉ J ∧ s = A j}) μ) :
    μ.real (B ∩ LocalLemma.avoid A Finset.univ) /
        μ.real (LocalLemma.avoid A Finset.univ) ≤
      μ.real B / ∏ j ∈ J, (1 - x j) := by
  have hpos := lll_avoid_positive μ A hA Γ hΓ x hx₀ hx₁ hP
  have hprod : 0 < ∏ j ∈ J, (1 - x j) :=
    Finset.prod_pos fun j _ => sub_pos.mpr (hx₁ j)
  apply (div_le_div_iff₀ hpos hprod).mpr
  simpa only [mul_comm] using conditional_lll_product μ A hA Γ hΓ x hx₀ hx₁ hP B J hBI

theorem exp_neg_two_le_one_sub (x : ℝ) (hx₀ : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hidentity : 1 - (1 - x)⁻¹ = -x / (1 - x) := by field_simp; ring
  have hbound : -2 * x ≤ -x / (1 - x) := by
    apply (le_div_iff₀ hpos).mpr
    nlinarith [mul_nonneg hx₀ (show 0 ≤ 1 / 2 - x by linarith)]
  rw [hidentity] at hlog
  exact (Real.exp_le_exp.mpr (hbound.trans hlog)).trans_eq (Real.exp_log hpos)

theorem exp_neg_two_sum_le_prod {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx₀ : ∀ i ∈ S, 0 ≤ x i) (hxhalf : ∀ i ∈ S, x i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ S, x i) ≤ ∏ i ∈ S, (1 - x i) := by
  have hpoint : ∀ i ∈ S, Real.exp (-2 * x i) ≤ 1 - x i :=
    fun i hi => exp_neg_two_le_one_sub (x i) (hx₀ i hi) (hxhalf i hi)
  have hprod := Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos (-2 * x i)).le) hpoint
  have heq : Real.exp (-2 * ∑ i ∈ S, x i) = ∏ i ∈ S, Real.exp (-2 * x i) := by
    rw [Finset.mul_sum, Real.exp_sum]
  exact heq.trans_le hprod

/-- The exponential version used when the total event weight touching the
extra event is bounded by `W`. -/
theorem conditional_lll_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (Γ : SimpleGraph (Fin n)) [DecidableRel Γ.Adj]
    (hΓ : LocalLemma.IsDependencyGraph μ A Γ) (x : Fin n → ℝ)
    (hx₀ : ∀ i, 0 ≤ x i) (hxhalf : ∀ i, x i ≤ 1 / 2)
    (hP : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j))
    (B : Set Ω) (J : Finset (Fin n)) (W : ℝ)
    (hBI : Indep (MeasurableSpace.generateFrom {B})
      (MeasurableSpace.generateFrom {s | ∃ j, j ∉ J ∧ s = A j}) μ)
    (hW : ∑ j ∈ J, x j ≤ W) :
    μ.real (B ∩ LocalLemma.avoid A Finset.univ) /
        μ.real (LocalLemma.avoid A Finset.univ) ≤ μ.real B * Real.exp (2 * W) := by
  have hx₁ : ∀ i, x i < 1 := fun i => lt_of_le_of_lt (hxhalf i) (by norm_num)
  have hratio := conditional_lll_ratio μ A hA Γ hΓ x hx₀ hx₁ hP B J hBI
  have hden := exp_neg_two_sum_le_prod J x (fun i _ => hx₀ i) (fun i _ => hxhalf i)
  have hdiv := div_le_div_of_nonneg_left (measureReal_nonneg (μ := μ) (s := B))
    (Real.exp_pos _) hden
  calc
    μ.real (B ∩ LocalLemma.avoid A Finset.univ) /
        μ.real (LocalLemma.avoid A Finset.univ) ≤
        μ.real B / ∏ j ∈ J, (1 - x j) := hratio
    _ ≤ μ.real B / Real.exp (-2 * ∑ j ∈ J, x j) := hdiv
    _ = μ.real B * Real.exp (2 * ∑ j ∈ J, x j) := by
      rw [show -2 * ∑ j ∈ J, x j = -(2 * ∑ j ∈ J, x j) by ring,
        Real.exp_neg, div_inv_eq_mul]
    _ ≤ μ.real B * Real.exp (2 * W) := by
      apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      apply Real.exp_le_exp.mpr
      linarith

end Erdos911
