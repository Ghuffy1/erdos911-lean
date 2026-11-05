import Erdos911.BlockCopyIncidence
import Erdos911.ConditionalMarkBudget

open MeasureTheory

namespace Erdos911

noncomputable def blockRichCopies {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W)
    (P : Finset (RectangleBlock W)) (b : ℕ) : Finset (F.Copy H) := by
  classical
  exact Finset.univ.filter (fun f => b ≤ (touchedBlocks P (copyRawEdges f)).card)

theorem mem_blockRichCopies {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W)
    (P : Finset (RectangleBlock W)) (b : ℕ) (f : F.Copy H) :
    f ∈ blockRichCopies F H P b ↔ b ≤ (touchedBlocks P (copyRawEdges f)).card := by
  classical
  simp only [blockRichCopies, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def noUnmarkedBlockRichCopies {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W)
    (P : Finset (RectangleBlock W)) (b : ℕ) : Set (P → Bool) :=
  avoidAll (fun f : blockRichCopies F H P b => fixedBits (touchedBlocks P (copyRawEdges f.val)) false)

/-- The local lemma marks at least one block in every block-rich copy,
with a conditional bound for each set of marked blocks. -/
theorem biased_block_copy_avoidance {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (P : Finset (RectangleBlock W)) (M : ℕ) (hP : BoundedEdgeBlocks P M)
    (b D : ℕ) (hD : ∀ w, H.degree w ≤ D)
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * b / 2) ≤ 1 / 2)
    (hincidence : (M * (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) : ℝ) *
      Real.exp (-p * b / 2) ≤ q) :
    0 < (bitProductMeasure P p hp₀ hp₁).real (noUnmarkedBlockRichCopies F H P b) ∧
      ∀ S : Finset P, (bitProductMeasure P p hp₀ hp₁).real
        (fixedBits S true ∩ noUnmarkedBlockRichCopies F H P b) /
          (bitProductMeasure P p hp₀ hp₁).real (noUnmarkedBlockRichCopies F H P b) ≤
            p ^ S.card * Real.exp (2 * (q * S.card)) := by
  classical
  let C := blockRichCopies F H P b
  let supports (f : C) := touchedBlocks P (copyRawEdges f.val)
  let A (f : C) := fixedBits (supports f) false
  let x := Real.exp (-p * b / 2)
  have hweights : ∀ B : P, ∑ f ∈ Finset.univ.filter (fun f => B ∈ supports f), x ≤ q := by
    intro B
    let uses := (Finset.univ : Finset C).filter (fun f => B ∈ supports f)
    let copies := (Finset.univ : Finset (F.Copy H)).filter
      (fun f => ¬Disjoint B.val.edges (copyRawEdges f))
    have hsub : uses.image Subtype.val ⊆ copies := by
      intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (mem_touchedBlocks P (copyRawEdges g.val) B).mp (Finset.mem_filter.mp hg).2⟩
    have hcount : uses.card ≤ M * (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) := by
      calc
        uses.card = (uses.image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ ≤ copies.card := Finset.card_le_card hsub
        _ ≤ _ := copy_block_incidence_bound F H hF D M hD B.val (hP.1 B.val B.property)
    have hreal : (uses.card : ℝ) ≤
        (M * (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) : ℝ) := by exact_mod_cast hcount
    simpa only [Finset.sum_const, nsmul_eq_mul, uses, x] using
      (mul_le_mul_of_nonneg_right hreal (Real.exp_pos _).le).trans hincidence
  have hprob : ∀ f : C, (bitProductMeasure P p hp₀ hp₁).real (A f) ≤
      x * Real.exp (-2 * (q * (supports f).card)) := by
    intro f
    change (bitProductMeasure P p hp₀ hp₁).real (fixedBits (supports f) false) ≤ _
    rw [bitProductMeasure_fixedBits]
    change (1 - p) ^ (supports f).card ≤ _
    have hb : b ≤ (supports f).card := (mem_blockRichCopies F H P b f.val).mp f.property
    have hweight : Real.exp (-p * (supports f).card / 2) ≤ x := by
      apply Real.exp_le_exp.mpr
      have hbreal : (b : ℝ) ≤ (supports f).card := by exact_mod_cast hb
      nlinarith
    exact (unmarked_probability_lll_bound p q hp₁ hq (supports f).card).trans
      (mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le)
  have h := coordinate_lll_from_exp_bounds_fintype
    (fun _ : P => bernoulliMarginal p hp₀ hp₁) A supports
    (fun f => fixedBits_depends (supports f) false) (fun _ => x) q
    (fun _ => (Real.exp_pos _).le) (fun _ => hhalf) hweights hprob
  refine ⟨h.1, ?_⟩
  intro S
  have hblue := h.2 (fixedBits S true) S (fixedBits_depends S true)
  change (bitProductMeasure P p hp₀ hp₁).real
      (fixedBits S true ∩ noUnmarkedBlockRichCopies F H P b) /
      (bitProductMeasure P p hp₀ hp₁).real (noUnmarkedBlockRichCopies F H P b) ≤
    (bitProductMeasure P p hp₀ hp₁).real (fixedBits S true) *
      Real.exp (2 * (q * S.card)) at hblue
  simpa only [bitProductMeasure_fixedBits, bernoulliWeight, ite_true] using hblue

theorem noUnmarkedBlockRichCopies_hits {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W)
    (P : Finset (RectangleBlock W)) (b : ℕ) (ω : P → Bool)
    (hω : ω ∈ noUnmarkedBlockRichCopies F H P b) (f : F.Copy H)
    (hf : b ≤ (touchedBlocks P (copyRawEdges f)).card) :
    ∃ B ∈ touchedBlocks P (copyRawEdges f), ω B = true := by
  classical
  have hnot := hω (⟨f, (mem_blockRichCopies F H P b f).mpr hf⟩ : blockRichCopies F H P b)
  by_contra h
  apply hnot
  intro B hB
  have hn : ω B ≠ true := fun ht => h ⟨B, hB, ht⟩
  cases hvalue : ω B <;> simp_all

/-- The chosen marks hit every block-rich copy while charging at most
twice the independent expected block capacity. -/
theorem exists_block_marks_with_budget {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (P : Finset (RectangleBlock W)) (M : ℕ) (hP : BoundedEdgeBlocks P M)
    (b D : ℕ) (hD : ∀ w, H.degree w ≤ D)
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * b / 2) ≤ 1 / 2)
    (hincidence : (M * (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) : ℝ) *
      Real.exp (-p * b / 2) ≤ q)
    (hfactor : Real.exp (2 * q) ≤ 2) (c : P → ℝ) (hc : ∀ B, 0 ≤ c B) :
    ∃ ω : P → Bool,
      (∑ B, if ω B = true then c B else 0) ≤ (2 * p) * ∑ B, c B ∧
      ∀ f : F.Copy H, b ≤ (touchedBlocks P (copyRawEdges f)).card →
        ∃ B ∈ touchedBlocks P (copyRawEdges f), ω B = true := by
  classical
  obtain ⟨hpositive, hconditional⟩ := biased_block_copy_avoidance F H hF P M hP
    b D hD p q hp₀ hp₁ hq hhalf hincidence
  have hmark : ∀ B : P, (bitProductMeasure P p hp₀ hp₁).real
      (fixedBits {B} true ∩ noUnmarkedBlockRichCopies F H P b) /
        (bitProductMeasure P p hp₀ hp₁).real (noUnmarkedBlockRichCopies F H P b) ≤ 2 * p := by
    intro B
    have h := hconditional {B}
    simp only [Finset.card_singleton, pow_one, Nat.cast_one, mul_one] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hfactor hp₀])
  obtain ⟨ω, hω, hcost⟩ := exists_conditional_mark_budget p hp₀ hp₁
    (noUnmarkedBlockRichCopies F H P b) hpositive c hc (2 * p) hmark
  exact ⟨ω, hcost, fun f hf => noUnmarkedBlockRichCopies_hits F H P b ω hω f hf⟩

end Erdos911
