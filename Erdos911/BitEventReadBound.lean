import Erdos911.FiniteRounds

open MeasureTheory

namespace Erdos911

theorem bitProductMeasure_real_singleton {E : Type*} [Fintype E]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (marks : E → Bool) :
    (bitProductMeasure E p hp₀ hp₁).real {marks} = ∏ e, bernoulliWeight p (marks e) := by
  calc
    _ = ∏ e, (bernoulliMarginal p hp₀ hp₁).real {marks e} := by
      simp only [Measure.real, bitProductMeasure, Measure.pi_singleton, ENNReal.toReal_prod]
    _ = _ := by simp only [bernoulliMarginal_real_singleton]

theorem bitProductMeasure_reindex {E F : Type*} [Fintype E] [Fintype F]
    (e : E ≃ F) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (A : Set (E → Bool)) :
    (bitProductMeasure E p hp₀ hp₁).real A =
      (bitProductMeasure F p hp₀ hp₁).real {marks | (fun i => marks (e i)) ∈ A} := by
  classical
  let φ : (F → Bool) ≃ (E → Bool) := e.symm.arrowCongr (Equiv.refl Bool)
  have hweight (marks : F → Bool) :
      (bitProductMeasure E p hp₀ hp₁).real {φ marks} =
        (bitProductMeasure F p hp₀ hp₁).real {marks} := by
    rw [bitProductMeasure_real_singleton, bitProductMeasure_real_singleton]
    change (∏ i : E, bernoulliWeight p (marks (e i))) = ∏ j : F, bernoulliWeight p (marks j)
    exact e.prod_comp (fun j : F => bernoulliWeight p (marks j))
  rw [finite_probability_eq_weighted_mean, finite_probability_eq_weighted_mean]
  unfold weightedMean
  calc
    _ = ∑ marks : F → Bool, (bitProductMeasure E p hp₀ hp₁).real {φ marks} *
        A.indicator (fun _ => 1) (φ marks) := (φ.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro marks _
      rw [hweight]
      congr 1

/-- The read bound applies to event indicators indexed by an arbitrary
finite Bernoulli coordinate type. -/
theorem bit_events_read_lower_tail {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (A : I → Set (E → Bool)) (D : I → Finset E) (r : ℕ)
    (hr : 0 < r) (hA : ∀ i, DependsOnlyOn (A i) (D i))
    (hread : ∀ e, (Finset.univ.filter (fun i => e ∈ D i)).card ≤ r) :
    (bitProductMeasure E p hp₀ hp₁).real
      {marks | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) marks) ≤
        (∑ i, (bitProductMeasure E p hp₀ hp₁).real (A i)) / 2} ≤
      Real.exp (-(∑ i, (bitProductMeasure E p hp₀ hp₁).real (A i)) / (8 * r)) := by
  classical
  let e := Fintype.equivFin E
  let X (i : I) (marks : Fin (Fintype.card E) → Bool) : ℝ :=
    (A i).indicator (fun _ => 1) (fun j => marks (e j))
  let D' (i : I) := (D i).image e
  have hX : ∀ i marks, X i marks = 0 ∨ X i marks = 1 := by
    intro i marks
    by_cases hi : (fun j => marks (e j)) ∈ A i <;> simp [X, Set.indicator, hi]
  have hD' : ∀ i, FunctionDependsOn (X i) (D' i) := by
    intro i marks marks' heq
    have heqE : ∀ j ∈ D i, marks (e j) = marks' (e j) := by
      intro j hj
      exact heq (e j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have heqE' : ∀ j ∈ D i, marks' (e j) = marks (e j) := fun j hj => (heqE j hj).symm
    by_cases hi : (fun j => marks (e j)) ∈ A i
    · have hi' := hA i _ _ heqE hi
      simp [X, Set.indicator, hi, hi']
    · have hi' : (fun j => marks' (e j)) ∉ A i := fun h => hi (hA i _ _ heqE' h)
      simp [X, Set.indicator, hi, hi']
  have hread' : ∀ j, (Finset.univ.filter (fun i => j ∈ D' i)).card ≤ r := by
    intro j
    have hmem (i : I) : j ∈ D' i ↔ e.symm j ∈ D i := by
      constructor
      · intro hj
        obtain ⟨k, hk, hkj⟩ := Finset.mem_image.mp hj
        have hkEq : k = e.symm j := by rw [← hkj, e.symm_apply_apply]
        exact hkEq ▸ hk
      · intro hj
        exact Finset.mem_image.mpr ⟨e.symm j, hj, e.apply_symm_apply j⟩
    have heq : (Finset.univ.filter (fun i => j ∈ D' i)) =
        Finset.univ.filter (fun i => e.symm j ∈ D i) := by
      ext i
      simp only [Finset.mem_filter, hmem]
    rw [heq]
    exact hread (e.symm j)
  have hmean (i : I) : cubeMean (fun _ : Fin (Fintype.card E) => p) (X i) =
      (bitProductMeasure E p hp₀ hp₁).real (A i) := by
    let B : Set (Fin (Fintype.card E) → Bool) := {marks | (fun j => marks (e j)) ∈ A i}
    have hXi : X i = B.indicator (fun _ => 1) := rfl
    rw [hXi]
    change cubeProbability (fun _ : Fin (Fintype.card E) => p) B = _
    rw [cubeProbability_eq_measureReal _ (fun _ => hp₀) (fun _ => hp₁)]
    exact (bitProductMeasure_reindex e p hp₀ hp₁ (A i)).symm
  have htail := read_lower_tail (fun _ : Fin (Fintype.card E) => p) X D' r
    (fun _ => hp₀) (fun _ => hp₁) hr hX hD' hread'
  simp_rw [hmean] at htail
  rw [bitProductMeasure_reindex e p hp₀ hp₁]
  simpa only [cubeProbability_eq_measureReal (fun _ : Fin (Fintype.card E) => p)
    (fun _ => hp₀) (fun _ => hp₁), X, bitProductMeasure, bernoulliCubeMeasure,
    Set.mem_ofPred_eq] using htail

theorem bit_events_few_successes {E I : Type*}
    [Fintype E] [DecidableEq E] [Fintype I]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (A : I → Set (E → Bool)) (D : I → Finset E) (r : ℕ)
    (hr : 0 < r) (hA : ∀ i, DependsOnlyOn (A i) (D i))
    (hread : ∀ e, (Finset.univ.filter (fun i => e ∈ D i)).card ≤ r)
    (β u : ℝ) (hprob : ∀ i, β ≤ (bitProductMeasure E p hp₀ hp₁).real (A i))
    (hu : u ≤ β * Fintype.card I / 2) :
    (bitProductMeasure E p hp₀ hp₁).real
      {marks | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) marks) ≤ u} ≤
      Real.exp (-(β * Fintype.card I) / (8 * r)) := by
  have hsum : β * Fintype.card I ≤ ∑ i, (bitProductMeasure E p hp₀ hp₁).real (A i) := by
    calc
      _ = ∑ _i : I, β := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hprob i)
  have hsub : {marks | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) marks) ≤ u} ⊆
      {marks | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) marks) ≤
        (∑ i, (bitProductMeasure E p hp₀ hp₁).real (A i)) / 2} := by
    intro marks hmarks
    have hmarks' : (∑ i, (A i).indicator (fun _ => (1 : ℝ)) marks) ≤ u := hmarks
    change (∑ i, (A i).indicator (fun _ => (1 : ℝ)) marks) ≤ _
    linarith
  apply (measureReal_mono hsub).trans
  apply (bit_events_read_lower_tail p hp₀ hp₁ A D r hr hA hread).trans
  apply Real.exp_le_exp.mpr
  have hrpos : (0 : ℝ) < 8 * r := by positivity
  exact div_le_div_of_nonneg_right (neg_le_neg hsum) hrpos.le

end Erdos911
