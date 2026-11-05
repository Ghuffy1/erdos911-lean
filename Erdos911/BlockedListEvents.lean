import Erdos911.BitEventReadBound
import Erdos911.ListCoveringRounds
import Erdos911.MatchedListIncidence

open MeasureTheory

namespace Erdos911

theorem bit_rounds_flatten_probability {I : Type*} [Fintype I]
    (h : ℕ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (A : Set (Fin h → I → Bool)) :
    (Measure.pi (fun _ : Fin h => bitProductMeasure I p hp₀ hp₁)).real A =
      (bitProductMeasure (Fin h × I) p hp₀ hp₁).real
        {marks | (fun round i => marks (round, i)) ∈ A} := by
  classical
  let φ := Equiv.curry (Fin h) I Bool
  have hweight (marks : Fin h × I → Bool) :
      (Measure.pi (fun _ : Fin h => bitProductMeasure I p hp₀ hp₁)).real {φ marks} =
        (bitProductMeasure (Fin h × I) p hp₀ hp₁).real {marks} := by
    calc
      _ = ∏ round : Fin h, (bitProductMeasure I p hp₀ hp₁).real {φ marks round} := by
        simp only [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
      _ = ∏ round : Fin h, ∏ i : I, bernoulliWeight p (marks (round, i)) := by
        simp only [bitProductMeasure_real_singleton]
        rfl
      _ = ∏ x : Fin h × I, bernoulliWeight p (marks x) :=
        (Fintype.prod_prod_type (fun x : Fin h × I => bernoulliWeight p (marks x))).symm
      _ = _ := (bitProductMeasure_real_singleton p hp₀ hp₁ marks).symm
  rw [finite_probability_eq_weighted_mean, finite_probability_eq_weighted_mean]
  unfold weightedMean
  calc
    _ = ∑ marks : Fin h × I → Bool,
        (Measure.pi (fun _ : Fin h => bitProductMeasure I p hp₀ hp₁)).real {φ marks} *
          A.indicator (fun _ => 1) (φ marks) := (φ.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro marks _
      rw [hweight]
      rfl

noncomputable def listBlockCoordinates {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : Finset W) : Finset (Fin h × I) := by
  classical
  exact Finset.univ.filter (fun x => ¬Disjoint (B x.2) L)

noncomputable def listBlocked {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : Finset W) : Set ((Fin h × I) → Bool) :=
  {marks | runRounds (uncoveredVertices B) L (fun round i => marks (round, i)) = ∅}

theorem uncoveredVertices_agree_on_list {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (L Y : Finset W) (hYL : Y ⊆ L) (marks marks' : I → Bool)
    (heq : ∀ i, ¬Disjoint (B i) L → marks i = marks' i) :
    uncoveredVertices B Y marks = uncoveredVertices B Y marks' := by
  classical
  have hmem (x : W) (hx : x ∈ Y) : x ∈ markedVertexUnion B marks ↔ x ∈ markedVertexUnion B marks' := by
    rw [mem_markedVertexUnion, mem_markedVertexUnion]
    constructor
    · rintro ⟨i, hi, hxB⟩
      exact ⟨i, (heq i (Finset.not_disjoint_iff.mpr ⟨x, hxB, hYL hx⟩)) ▸ hi, hxB⟩
    · rintro ⟨i, hi, hxB⟩
      exact ⟨i, (heq i (Finset.not_disjoint_iff.mpr ⟨x, hxB, hYL hx⟩)).symm ▸ hi, hxB⟩
  ext x
  by_cases hx : x ∈ Y
  · simp only [uncoveredVertices, Finset.mem_sdiff, hx, true_and, hmem x hx]
  · simp only [uncoveredVertices, Finset.mem_sdiff, hx, false_and]

theorem run_uncovered_agree_on_list {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (L : Finset W) :
    ∀ (h : ℕ) (Y : Finset W), Y ⊆ L → ∀ marks marks' : Fin h → I → Bool,
      (∀ round i, ¬Disjoint (B i) L → marks round i = marks' round i) →
      runRounds (uncoveredVertices B) Y marks = runRounds (uncoveredVertices B) Y marks' := by
  intro h
  induction h with
  | zero => intros; rfl
  | succ h ih =>
    intro Y hYL marks marks' heq
    simp only [runRounds]
    rw [uncoveredVertices_agree_on_list B L Y hYL (marks 0) (marks' 0) (heq 0)]
    exact ih _ ((uncoveredVertices_subset B Y (marks' 0)).trans hYL) _ _
      (fun round => heq round.succ)

theorem listBlocked_depends {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : Finset W) :
    DependsOnlyOn (listBlocked B h L) (listBlockCoordinates B h L) := by
  classical
  intro marks marks' heq hblocked
  have hagree := run_uncovered_agree_on_list B L h L (Finset.Subset.refl _)
    (fun round i => marks (round, i)) (fun round i => marks' (round, i))
    (fun round i hi => heq (round, i) (by
      simp only [listBlockCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi))
  change runRounds (uncoveredVertices B) L (fun round i => marks (round, i)) = ∅ at hblocked
  change runRounds (uncoveredVertices B) L (fun round i => marks' (round, i)) = ∅
  exact hagree.symm.trans hblocked

theorem listBlocked_round_probability {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : Finset W) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (bitProductMeasure (Fin h × I) p hp₀ hp₁).real (listBlocked B h L) =
      (Measure.pi (fun _ : Fin h => bitProductMeasure I p hp₀ hp₁)).real
        {marks | runRounds (uncoveredVertices B) L marks = ∅} := by
  rw [bit_rounds_flatten_probability]
  rfl

theorem listBlockCoordinates_read_bound {J I W : Type*}
    [Fintype J] [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (Q : SimpleGraph W) [DecidableRel Q.Adj] (L : J → Finset W)
    (f : J → W) (hf : Function.Injective f) (hmem : ∀ j, f j ∈ L j)
    (hclique : ∀ j, ∀ x ∈ L j, ∀ y ∈ L j, x ≠ y → Q.Adj x y)
    (q : ℕ) (B : I → Finset W) (hB : ∀ i, (B i).card ≤ q)
    (hdegree : ∀ i y, y ∈ B i → Q.degree y < q) (h : ℕ) (x : Fin h × I) :
    (Finset.univ.filter (fun j => x ∈ listBlockCoordinates B h (L j))).card ≤ q * q := by
  classical
  have heq : (Finset.univ.filter (fun j => x ∈ listBlockCoordinates B h (L j))) =
      Finset.univ.filter (fun j => ¬Disjoint (B x.2) (L j)) := by
    ext j
    simp only [listBlockCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq]
  exact matched_lists_read_bound_on Q L f hf hmem hclique q (B x.2) (hB x.2) (hdegree x.2)

/-- Overlapping lists with injective representatives satisfy the robust
lower-tail estimate for the number of completely blocked lists. -/
theorem matched_lists_few_blocked {J I W : Type*}
    [Fintype J] [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (Q : SimpleGraph W) [DecidableRel Q.Adj] (L : J → Finset W)
    (f : J → W) (hf : Function.Injective f) (hmem : ∀ j, f j ∈ L j)
    (hclique : ∀ j, ∀ x ∈ L j, ∀ y ∈ L j, x ≠ y → Q.Adj x y)
    (q : ℕ) (hq : 0 < q) (B : I → Finset W) (hB : ∀ i, (B i).card ≤ q)
    (hdegree : ∀ i y, y ∈ B i → Q.degree y < q) (h : ℕ)
    (p β u : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hprob : ∀ j, β ≤ (bitProductMeasure (Fin h × I) p hp₀ hp₁).real (listBlocked B h (L j)))
    (hu : u ≤ β * Fintype.card J / 2) :
    (bitProductMeasure (Fin h × I) p hp₀ hp₁).real
      {marks | (∑ j, (listBlocked B h (L j)).indicator (fun _ => (1 : ℝ)) marks) ≤ u} ≤
      Real.exp (-(β * Fintype.card J) / (8 * (q * q : ℕ))) := by
  exact bit_events_few_successes p hp₀ hp₁ (fun j => listBlocked B h (L j))
    (fun j => listBlockCoordinates B h (L j)) (q * q) (Nat.mul_pos hq hq)
    (fun j => listBlocked_depends B h (L j))
    (fun x => listBlockCoordinates_read_bound Q L f hf hmem hclique q B hB hdegree h x)
    β u hprob hu

end Erdos911
