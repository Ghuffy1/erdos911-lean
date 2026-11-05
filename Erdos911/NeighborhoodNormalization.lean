import Erdos911.UniformSubsets
import Erdos911.ProductIndicators
import Erdos911.CoordinateAvoidance

open MeasureTheory

namespace Erdos911

noncomputable def subsetInclusionProbability {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (x : V) : ℝ :=
  if x ∈ N then (q : ℝ) / N.card else 0

theorem subsetInclusionProbability_nonneg {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (x : V) : 0 ≤ subsetInclusionProbability N q x := by
  unfold subsetInclusionProbability
  split_ifs <;> positivity

theorem subsetInclusionProbability_le_one {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (hq : q ≤ N.card) (x : V) :
    subsetInclusionProbability N q x ≤ 1 := by
  unfold subsetInclusionProbability
  split_ifs with hx
  · have hN : (0 : ℝ) < N.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
    apply (div_le_one hN).mpr
    exact_mod_cast hq
  · norm_num

noncomputable def subsetMembership {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (x : V) (S : FixedSizeSubset N q) : Bool :=
  decide (x ∈ S.val)

theorem subsetMembership_probability {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (hq : q ≤ N.card) (x : V) :
    (uniformSubsetMeasure N q hq).real ((subsetMembership N q x) ⁻¹' {true}) =
      subsetInclusionProbability N q x := by
  have hevent : (subsetMembership N q x) ⁻¹' {true} = {S | x ∈ S.val} := by
    ext S
    simp [subsetMembership]
  rw [hevent]
  by_cases hx : x ∈ N
  · simpa [subsetInclusionProbability, hx] using uniformSubsetMeasure_inclusion N q hq x hx
  · simpa [subsetInclusionProbability, hx] using uniformSubsetMeasure_outside N q hq x hx

abbrev NeighborhoodChoice {m n : ℕ} (N : Fin n → Finset (Fin m)) (q : ℕ) :=
  ∀ y, FixedSizeSubset (N y) q

noncomputable def neighborhoodMean {m n : ℕ} (N : Fin n → Finset (Fin m))
    (q : ℕ) (x : Fin m) : ℝ :=
  ∑ y, subsetInclusionProbability (N y) q x

def chosenLeftDegree {m n : ℕ} {N : Fin n → Finset (Fin m)} {q : ℕ}
    (ω : NeighborhoodChoice N q) (x : Fin m) : ℕ :=
  ∑ y, if x ∈ (ω y).val then 1 else 0

theorem chosenLeftDegree_eq_card {m n : ℕ} {N : Fin n → Finset (Fin m)} {q : ℕ}
    (ω : NeighborhoodChoice N q) (x : Fin m) :
    chosenLeftDegree ω x = (Finset.univ.filter (fun y => x ∈ (ω y).val)).card := by
  simp [chosenLeftDegree]

theorem chosenLeftDegree_real {m n : ℕ} {N : Fin n → Finset (Fin m)} {q : ℕ}
    (ω : NeighborhoodChoice N q) (x : Fin m) :
    (chosenLeftDegree ω x : ℝ) =
      sampleCount Finset.univ (fun y => subsetMembership (N y) q x (ω y)) := by
  unfold sampleCount
  rw [Finset.sum_coe_sort (Finset.univ : Finset (Fin n))
    (fun y => coordinateIndicator y (fun y => subsetMembership (N y) q x (ω y)))]
  simp [chosenLeftDegree, coordinateIndicator, subsetMembership]

theorem neighborhood_lower_tail {m n : ℕ} (N : Fin n → Finset (Fin m))
    (q : ℕ) (hq : ∀ y, q ≤ (N y).card) (x : Fin m) :
    (Measure.pi (fun y => uniformSubsetMeasure (N y) q (hq y))).real
        {ω : NeighborhoodChoice N q | (chosenLeftDegree ω x : ℝ) ≤
          neighborhoodMean N q x / 2} ≤ Real.exp (-neighborhoodMean N q x / 8) := by
  have h := product_indicator_lower_tail
    (fun y => uniformSubsetMeasure (N y) q (hq y))
    (fun y => subsetMembership (N y) q x)
    (fun y => measurable_of_countable _)
    (fun y => subsetInclusionProbability (N y) q x)
    (fun y => subsetInclusionProbability_nonneg (N y) q x)
    (fun y => subsetInclusionProbability_le_one (N y) q (hq y) x)
    (fun y => subsetMembership_probability (N y) q (hq y) x) Finset.univ
  have hm : (∑ y : (Finset.univ : Finset (Fin n)),
      subsetInclusionProbability (N y) q x) = neighborhoodMean N q x := by
    rw [Finset.sum_coe_sort (Finset.univ : Finset (Fin n))
      (fun y => subsetInclusionProbability (N y) q x)]
    rfl
  rw [hm] at h
  simpa only [← chosenLeftDegree_real] using h

theorem neighborhood_lower_tail_depends {m n : ℕ} (N : Fin n → Finset (Fin m))
    (q : ℕ) (x : Fin m) :
    DependsOnlyOn
      {ω : NeighborhoodChoice N q | (chosenLeftDegree ω x : ℝ) ≤ neighborhoodMean N q x / 2}
      (Finset.univ.filter (fun y => x ∈ N y)) := by
  intro ω ω' heq hω
  have hdegrees : chosenLeftDegree ω x = chosenLeftDegree ω' x := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : x ∈ N y
    · rw [heq y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)]
    · have hωx : x ∉ (ω y).val :=
        fun h => hx ((Finset.mem_powersetCard.mp (ω y).property).1 h)
      have hω'x : x ∉ (ω' y).val :=
        fun h => hx ((Finset.mem_powersetCard.mp (ω' y).property).1 h)
      simp only [ite_eq_right hωx, ite_eq_right hω'x]
  change (chosenLeftDegree ω x : ℝ) ≤ neighborhoodMean N q x / 2 at hω
  change (chosenLeftDegree ω' x : ℝ) ≤ neighborhoodMean N q x / 2
  rw [← hdegrees]
  exact hω

theorem neighborhoodMean_lower_bound {m n : ℕ} (N : Fin n → Finset (Fin m))
    (q b : ℕ) (hb : ∀ y, (N y).card ≤ b) (x : Fin m) :
    (q : ℝ) / b * (Finset.univ.filter (fun y => x ∈ N y)).card ≤
      neighborhoodMean N q x := by
  classical
  calc
    (q : ℝ) / b * (Finset.univ.filter (fun y => x ∈ N y)).card =
        ∑ y ∈ Finset.univ.filter (fun y => x ∈ N y), (q : ℝ) / b := by
      simp [mul_comm]
    _ = ∑ y, if x ∈ N y then (q : ℝ) / b else 0 := by rw [Finset.sum_filter]
    _ ≤ neighborhoodMean N q x := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hx : x ∈ N y
      · simp only [ite_eq_left hx, subsetInclusionProbability]
        have hN : (0 : ℝ) < (N y).card := by
          exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg q) hN (by exact_mod_cast hb y)
      · simp [hx, subsetInclusionProbability]

/-- Independent uniform choices of exactly q neighbors at every right vertex
can preserve more than half of every left expectation simultaneously. -/
theorem exists_neighborhood_normalization {m n : ℕ} (N : Fin n → Finset (Fin m))
    (q a b : ℕ) (M : ℝ) (hq : ∀ y, q ≤ (N y).card)
    (ha : ∀ x, (Finset.univ.filter (fun y => x ∈ N y)).card ≤ a)
    (hb : ∀ y, (N y).card ≤ b)
    (hM : ∀ x, M ≤ neighborhoodMean N q x)
    (hc : Real.exp 1 * Real.exp (-M / 8) * ((a * b : ℕ) + 1) ≤ 1) :
    ∃ S : Fin n → Finset (Fin m),
      (∀ y, S y ⊆ N y ∧ (S y).card = q) ∧
        ∀ x, neighborhoodMean N q x / 2 <
          ((Finset.univ.filter (fun y => x ∈ S y)).card : ℝ) := by
  classical
  let A := fun x : Fin m =>
    {ω : NeighborhoodChoice N q | (chosenLeftDegree ω x : ℝ) ≤ neighborhoodMean N q x / 2}
  let D := fun x : Fin m => Finset.univ.filter (fun y => x ∈ N y)
  have hP : ∀ x, (Measure.pi (fun y => uniformSubsetMeasure (N y) q (hq y))).real (A x) ≤
      Real.exp (-M / 8) := by
    intro x
    apply (neighborhood_lower_tail N q hq x).trans
    apply Real.exp_le_exp.mpr
    linarith [hM x]
  have hread : ∀ y, (Finset.univ.filter (fun x => y ∈ D x)).card ≤ b := by
    intro y
    have heq : Finset.univ.filter (fun x => y ∈ D x) = N y := by
      ext x
      simp [D]
    rw [heq]
    exact hb y
  obtain ⟨ω, hω⟩ := exists_avoiding_coordinate_events
    (fun y => uniformSubsetMeasure (N y) q (hq y)) A D
    (neighborhood_lower_tail_depends N q) (Real.exp (-M / 8)) a b hP ha hread hc
  refine ⟨fun y => (ω y).val, ?_, ?_⟩
  · intro y
    exact Finset.mem_powersetCard.mp (ω y).property
  · intro x
    have hx : neighborhoodMean N q x / 2 < (chosenLeftDegree ω x : ℝ) :=
      lt_of_not_ge (hω x)
    simpa only [chosenLeftDegree_eq_card] using hx

/-- Degree form of the normalization used after peeling a bipartite band. -/
theorem exists_degree_normalization {m n : ℕ} (N : Fin n → Finset (Fin m))
    (q a b r : ℕ) (hq : ∀ y, q ≤ (N y).card)
    (ha : ∀ x, (Finset.univ.filter (fun y => x ∈ N y)).card ≤ a)
    (hb : ∀ y, (N y).card ≤ b)
    (hr : ∀ x, r ≤ (Finset.univ.filter (fun y => x ∈ N y)).card)
    (hc : Real.exp 1 * Real.exp (-((q : ℝ) / b * r) / 8) * ((a * b : ℕ) + 1) ≤ 1) :
    ∃ S : Fin n → Finset (Fin m),
      (∀ y, S y ⊆ N y ∧ (S y).card = q) ∧
        ∀ x, (q : ℝ) / b * r / 2 <
          ((Finset.univ.filter (fun y => x ∈ S y)).card : ℝ) := by
  have hM : ∀ x, (q : ℝ) / b * r ≤ neighborhoodMean N q x := by
    intro x
    apply le_trans _ (neighborhoodMean_lower_bound N q b hb x)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr x) (by positivity)
  obtain ⟨S, hS, hleft⟩ := exists_neighborhood_normalization N q a b
    ((q : ℝ) / b * r) hq ha hb hM hc
  refine ⟨S, hS, fun x => lt_of_le_of_lt ?_ (hleft x)⟩
  exact div_le_div_of_nonneg_right (hM x) (by norm_num)

end Erdos911
