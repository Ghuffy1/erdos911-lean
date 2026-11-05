import Erdos911.FiniteRounds

open MeasureTheory

namespace Erdos911

noncomputable def markedVertexUnion {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (marks : I → Bool) : Finset W := by
  classical
  exact (Finset.univ.filter (fun i => marks i = true)).biUnion B

noncomputable def uncoveredVertices {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (Y : Finset W) (marks : I → Bool) : Finset W :=
  Y \ markedVertexUnion B marks

theorem mem_markedVertexUnion {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (marks : I → Bool) (x : W) :
    x ∈ markedVertexUnion B marks ↔ ∃ i, marks i = true ∧ x ∈ B i := by
  classical
  simp only [markedVertexUnion, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]

theorem uncoveredVertices_subset {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (Y : Finset W) (marks : I → Bool) : uncoveredVertices B Y marks ⊆ Y :=
  Finset.sdiff_subset

theorem uncoveredVertices_subset_sdiff {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (Y : Finset W) (marks : I → Bool) (i : I) (hi : marks i = true) :
    uncoveredVertices B Y marks ⊆ Y \ B i := by
  intro x hx
  obtain ⟨hxY, hxnot⟩ := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨hxY, fun hxB => hxnot ((mem_markedVertexUnion B marks x).mpr ⟨i, hi, hxB⟩)⟩

theorem uncoveredVertices_empty {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (marks : I → Bool) : uncoveredVertices B ∅ marks = ∅ := by
  simp only [uncoveredVertices, Finset.empty_sdiff]

theorem marked_family_probability {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (A : Finset I) :
    (bitProductMeasure I p hp₀ hp₁).real {marks | ∃ i ∈ A, marks i = true} =
      1 - (1 - p) ^ A.card := by
  classical
  have heq : {marks : I → Bool | ∃ i ∈ A, marks i = true} = (fixedBits A false)ᶜ := by
    ext marks
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, fixedBits]
    constructor
    · rintro ⟨i, hi, hmark⟩ hall
      have hfalse := hall i hi
      simp_all
    · intro hn
      push Not at hn
      obtain ⟨i, hi, hnot⟩ := hn
      refine ⟨i, hi, ?_⟩
      cases hmark : marks i with
      | false => exact False.elim (hnot hmark)
      | true => rfl
  rw [heq, probReal_compl_eq_one_sub (Set.toFinite _).measurableSet, bitProductMeasure_fixedBits]
  rfl

/-- Any one marked member of the supplied family gives the requested
decrease in the number of uncovered candidates. -/
theorem uncovered_step_probability {I W : Type*} [Fintype I] [DecidableEq I] [DecidableEq W]
    (B : I → Finset W) (Y : Finset W) (A : Finset I) (p N R : ℝ)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hN : N ≤ A.card)
    (hdecrease : ∀ i ∈ A, ((Y \ B i).card : ℝ) ≤ R) :
    1 - Real.exp (-p * N) ≤
      (bitProductMeasure I p hp₀ hp₁).real {marks | ((uncoveredVertices B Y marks).card : ℝ) ≤ R} := by
  have hsub : {marks : I → Bool | ∃ i ∈ A, marks i = true} ⊆
      {marks | ((uncoveredVertices B Y marks).card : ℝ) ≤ R} := by
    rintro marks ⟨i, hi, hmark⟩
    have hcard : ((uncoveredVertices B Y marks).card : ℝ) ≤ (Y \ B i).card := by
      exact_mod_cast Finset.card_le_card (uncoveredVertices_subset_sdiff B Y marks i hmark)
    exact hcard.trans (hdecrease i hi)
  have hexp : (1 - p) ^ A.card ≤ Real.exp (-p * N) :=
    (unmarked_probability_exp_bound p hp₁ A.card).trans
      (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hN hp₀]))
  have hprob := measureReal_mono (μ := bitProductMeasure I p hp₀ hp₁) hsub
  rw [marked_family_probability p hp₀ hp₁ A] at hprob
  linarith

noncomputable def coverableInRounds {W : Type*} [DecidableEq W]
    (Z : Finset W) (δ : ℝ) (s : ℕ) : ℕ → Set (Finset W)
  | 0 => {Y | Y ⊆ Z ∧ Y = ∅}
  | h + 1 => {Y | Y ⊆ Z ∧ δ ^ h * (Y.card : ℝ) ≤ s}

/-- Small residual lists can be covered in one successful round. Larger
lists contract by a fixed factor on each successful round. -/
theorem independent_list_cover_probability {I W : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq W]
    (B : I → Finset W) (Z : Finset W) (s h : ℕ) (δ p N β : ℝ)
    (hδ : 0 ≤ δ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hβ : 0 ≤ β)
    (hβbound : β ≤ 1 - Real.exp (-p * N))
    (hsmall : ∀ Y ⊆ Z, Y.Nonempty → (Y.card : ℝ) ≤ s →
      ∃ A : Finset I, N ≤ (A.card : ℝ) ∧ ∀ i ∈ A, Y ⊆ B i)
    (hshrink : ∀ Y ⊆ Z, Y.Nonempty →
      ∃ A : Finset I, N ≤ (A.card : ℝ) ∧ ∀ i ∈ A, ((Y \ B i).card : ℝ) ≤ δ * Y.card)
    (hinitial : δ ^ h * (Z.card : ℝ) ≤ s) :
    β ^ (h + 1) ≤
      (Measure.pi (fun _ : Fin (h + 1) => bitProductMeasure I p hp₀ hp₁)).real
        {marks | runRounds (uncoveredVertices B) Z marks = ∅} := by
  classical
  let μ := bitProductMeasure I p hp₀ hp₁
  let P := coverableInRounds Z δ s
  have hβone : β ≤ 1 := by linarith [Real.exp_pos (-p * N)]
  have hstep : ∀ r Y, Y ∈ P (r + 1) →
      β ≤ μ.real {marks | uncoveredVertices B Y marks ∈ P r} := by
    intro r Y hY
    have hYZ : Y ⊆ Z := hY.1
    by_cases hYe : Y = ∅
    · subst Y
      have hempty : ∀ marks, uncoveredVertices B ∅ marks ∈ P r := by
        intro marks
        rw [uncoveredVertices_empty]
        cases r with
        | zero => exact ⟨Finset.empty_subset _, rfl⟩
        | succ r => exact ⟨Finset.empty_subset _, by simp [Finset.card_empty]⟩
      have heq : {marks | uncoveredVertices B ∅ marks ∈ P r} = (Set.univ : Set (I → Bool)) := by
        ext marks
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact hempty marks
      rw [heq, probReal_univ]
      exact hβone
    have hYne : Y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hYe
    cases r with
    | zero =>
      obtain ⟨A, hA, hcover⟩ := hsmall Y hYZ hYne (by simpa only [P, coverableInRounds, pow_zero, one_mul] using hY.2)
      have hprob := uncovered_step_probability B Y A p N 0 hp₀ hp₁ hA (by
        intro i hi
        rw [Finset.sdiff_eq_empty_iff_subset.mpr (hcover i hi)]
        norm_num)
      apply (hβbound.trans hprob).trans
      apply measureReal_mono (μ := bitProductMeasure I p hp₀ hp₁)
      intro marks hmarks
      have hempty : uncoveredVertices B Y marks = ∅ := by
        apply Finset.card_eq_zero.mp
        have hcard : ((uncoveredVertices B Y marks).card : ℝ) ≤ 0 := hmarks
        have hnat : (uncoveredVertices B Y marks).card ≤ 0 := by exact_mod_cast hcard
        omega
      exact ⟨(uncoveredVertices_subset B Y marks).trans hYZ, hempty⟩
    | succ r =>
      obtain ⟨A, hA, hdecrease⟩ := hshrink Y hYZ hYne
      have hprob := uncovered_step_probability B Y A p N (δ * Y.card) hp₀ hp₁ hA hdecrease
      apply (hβbound.trans hprob).trans
      apply measureReal_mono (μ := bitProductMeasure I p hp₀ hp₁)
      intro marks hmarks
      refine ⟨(uncoveredVertices_subset B Y marks).trans hYZ, ?_⟩
      have hbound := mul_le_mul_of_nonneg_left hmarks (pow_nonneg hδ r)
      have hstart : δ ^ (r + 1) * (Y.card : ℝ) ≤ s := hY.2
      change δ ^ r * ((uncoveredVertices B Y marks).card : ℝ) ≤ s
      rw [pow_succ] at hstart
      nlinarith only [hbound, hstart]
  have hterminal : P 0 ⊆ {Y | Y = ∅} := fun _ hY => hY.2
  exact independent_rounds_reach_probability (uncoveredVertices B) μ P {Y | Y = ∅}
    hterminal β hβ hstep (h + 1) Z ⟨Finset.Subset.refl _, hinitial⟩

end Erdos911
