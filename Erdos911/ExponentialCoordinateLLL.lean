import Erdos911.CoordinateAvoidance

open MeasureTheory

namespace Erdos911

def avoidAll {I Ω : Type*} (A : I → Set Ω) : Set Ω := {ω | ∀ i, ω ∉ A i}

/-- Per-coordinate weight budgets and exponential event bounds imply the
local-lemma product condition, together with its conditional estimate. -/
theorem coordinate_lll_from_exp_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSingletonClass (β i)]
    (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)] {n : ℕ}
    (A : Fin n → Set (∀ i, β i)) (S : Fin n → Finset ι)
    (hA : ∀ j, DependsOnlyOn (A j) (S j))
    (x : Fin n → ℝ) (q : ℝ) (hx₀ : ∀ j, 0 ≤ x j) (hxhalf : ∀ j, x j ≤ 1 / 2)
    (hq : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), x j ≤ q)
    (hP : ∀ j, (Measure.pi μ).real (A j) ≤ x j * Real.exp (-2 * (q * (S j).card))) :
    0 < (Measure.pi μ).real (LocalLemma.avoid A Finset.univ) ∧
      ∀ (B : Set (∀ i, β i)) (T : Finset ι), DependsOnlyOn B T →
        (Measure.pi μ).real (B ∩ LocalLemma.avoid A Finset.univ) /
          (Measure.pi μ).real (LocalLemma.avoid A Finset.univ) ≤
            (Measure.pi μ).real B * Real.exp (2 * (q * T.card)) := by
  classical
  let Γ := coordinateOverlapGraph S
  have hΓ : ∀ i j, j ≠ i → ¬Γ.Adj i j → Disjoint (S i) (S j) := by
    intro i j hji hn
    by_contra hdis
    exact hn ⟨hji.symm, hdis⟩
  have hproduct : ∀ i, (Measure.pi μ).real (A i) ≤
      x i * ∏ j ∈ Γ.neighborFinset i, (1 - x j) := by
    intro i
    have hsub : Γ.neighborFinset i ⊆
        Finset.univ.filter (fun j => ¬Disjoint (S i) (S j)) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Γ.mem_neighborFinset i j).mp hj).2⟩
    have hsum : ∑ j ∈ Γ.neighborFinset i, x j ≤ q * (S i).card := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hx₀ j)).trans
      exact touching_weight_sum_le (S i) S x q hx₀ (fun z _ => hq z)
    have hexp : Real.exp (-2 * (q * (S i).card)) ≤
        Real.exp (-2 * ∑ j ∈ Γ.neighborFinset i, x j) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hprod := exp_neg_two_sum_le_prod (Γ.neighborFinset i) x
      (fun j _ => hx₀ j) (fun j _ => hxhalf j)
    exact (hP i).trans (mul_le_mul_of_nonneg_left (hexp.trans hprod) (hx₀ i))
  have hdep := product_dependency_graph μ A S hA Γ hΓ
  refine ⟨lll_avoid_positive (Measure.pi μ) A
    (fun i => (Set.toFinite (A i)).measurableSet) Γ hdep x hx₀
    (fun i => lt_of_le_of_lt (hxhalf i) (by norm_num)) hproduct, ?_⟩
  intro B T hB
  exact conditional_lll_coordinates μ A S hA Γ hΓ x hx₀ hxhalf hproduct B T hB q
    (fun i _ => hq i)

/-- The coordinate local lemma with an arbitrary finite event index. -/
theorem coordinate_lll_from_exp_bounds_fintype {ι I : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype I]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSingletonClass (β i)]
    (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : I → Set (∀ i, β i)) (S : I → Finset ι)
    (hA : ∀ j, DependsOnlyOn (A j) (S j))
    (x : I → ℝ) (q : ℝ) (hx₀ : ∀ j, 0 ≤ x j) (hxhalf : ∀ j, x j ≤ 1 / 2)
    (hq : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), x j ≤ q)
    (hP : ∀ j, (Measure.pi μ).real (A j) ≤ x j * Real.exp (-2 * (q * (S j).card))) :
    0 < (Measure.pi μ).real (avoidAll A) ∧
      ∀ (B : Set (∀ i, β i)) (T : Finset ι), DependsOnlyOn B T →
        (Measure.pi μ).real (B ∩ avoidAll A) / (Measure.pi μ).real (avoidAll A) ≤
          (Measure.pi μ).real B * Real.exp (2 * (q * T.card)) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hq' : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S (e j)), x (e j) ≤ q := by
    intro i
    have heq : (∑ j ∈ Finset.univ.filter (fun j => i ∈ S (e j)), x (e j)) =
        ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), x j := by
      simp only [Finset.sum_filter]
      exact e.sum_comp (fun j => if i ∈ S j then x j else 0)
    exact heq.trans_le (hq i)
  have hgood : LocalLemma.avoid (fun j => A (e j)) Finset.univ = avoidAll A := by
    ext ω
    simp only [LocalLemma.avoid, Set.mem_iInter, Finset.mem_univ, forall_true_left,
      Set.mem_compl_iff, avoidAll, Set.mem_ofPred_eq]
    constructor
    · intro h i
      obtain ⟨j, rfl⟩ := e.surjective i
      exact h j
    · intro h j
      exact h (e j)
  have h := coordinate_lll_from_exp_bounds μ (fun j => A (e j)) (fun j => S (e j))
    (fun j => hA (e j)) (fun j => x (e j)) q (fun j => hx₀ (e j))
    (fun j => hxhalf (e j)) hq' (fun j => hP (e j))
  simpa only [hgood] using h

end Erdos911
