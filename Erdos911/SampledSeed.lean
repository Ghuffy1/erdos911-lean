import Erdos911.SampleAlteration
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos911

/-- A sample augmented by every failed role is a dominating set, provided
failure includes having no sampled neighbor. The size uses only marginal
failure probabilities. -/
theorem exists_dominating_repair_set {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (p : Fin n → ℝ) (A : Fin n → Set (Fin n → Bool))
    (ε : Fin n → ℝ) (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hA : ∀ v, cubeProbability p (A v) ≤ ε v)
    (hfailure : ∀ v ω, (∀ w ∈ G.neighborFinset v, ω w = false) → ω ∈ A v) :
    ∃ (ω : Fin n → Bool) (S : Finset (Fin n)),
      (∀ v, ω v = true → v ∈ S) ∧
        (∀ v, ω ∈ A v → v ∈ S) ∧
          (∀ v, v ∈ S ∨ ∃ w ∈ S, G.Adj v w) ∧
            (S.card : ℝ) ≤ (∑ j, p j) + ∑ v, ε v := by
  classical
  obtain ⟨ω, hbudget⟩ := exists_sample_repair_budget p A ε hp₀ hp₁ hA
  let T := Finset.univ.filter (fun v => ω v = true)
  let R := Finset.univ.filter (fun v => ω ∈ A v)
  let S := T ∪ R
  have hsample : ∀ v, ω v = true → v ∈ S := by
    intro v hv
    exact Finset.mem_union_left R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
  have hrepair : ∀ v, ω ∈ A v → v ∈ S := by
    intro v hv
    exact Finset.mem_union_right T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
  refine ⟨ω, S, hsample, hrepair, ?_, ?_⟩
  · intro v
    by_cases hv : ω ∈ A v
    · exact Or.inl (hrepair v hv)
    · right
      have hneighbor : ∃ w ∈ G.neighborFinset v, ω w = true := by
        by_contra hn
        apply hv
        apply hfailure v ω
        intro w hw
        cases he : ω w with
        | false => rfl
        | true => exact False.elim (hn ⟨w, hw, he⟩)
      obtain ⟨w, hw, htrue⟩ := hneighbor
      exact ⟨w, hsample w htrue, (G.mem_neighborFinset v w).mp hw⟩
  · have hcard : (S.card : ℝ) ≤ T.card + R.card := by
      exact_mod_cast Finset.card_union_le T R
    have hT : (T.card : ℝ) = sampleCount Finset.univ ω :=
      (sampleCount_eq_card Finset.univ ω).symm
    have hR : R.card = repairCount A ω := rfl
    rw [hT, hR] at hcard
    exact hcard.trans hbudget

theorem exists_small_dominating_set {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (d : ℕ) (hd : ∀ v, d ≤ G.degree v)
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ∃ S : Finset (Fin n), (∀ v, v ∈ S ∨ ∃ w ∈ S, G.Adj v w) ∧
      (S.card : ℝ) ≤ n * (p + Real.exp (-p * d)) := by
  let A := fun v => {ω : Fin n → Bool | ∀ w ∈ G.neighborFinset v, ω w = false}
  have hA : ∀ v, cubeProbability (fun _ => p) (A v) ≤ Real.exp (-p * d) := by
    intro v
    apply (empty_sample_probability_le p (G.neighborFinset v) hp₀ hp₁).trans
    apply Real.exp_le_exp.mpr
    have hdegree : (d : ℝ) ≤ G.degree v := by exact_mod_cast hd v
    rw [G.card_neighborFinset_eq_degree]
    nlinarith
  obtain ⟨ω, S, _, _, hdom, hsize⟩ := exists_dominating_repair_set G (fun _ => p) A
    (fun _ => Real.exp (-p * d)) (fun _ => hp₀) (fun _ => hp₁) hA
    (fun _ _ h => h)
  refine ⟨S, hdom, ?_⟩
  simpa [mul_add] using hsize

end Erdos911
