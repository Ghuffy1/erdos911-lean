import Erdos911.BiasedBits
import Erdos911.ExponentialCoordinateLLL
import Erdos911.AnchoredCopyCounting
import Erdos911.ColoringFirstMoment

open MeasureTheory

namespace Erdos911

noncomputable def noRedCopies {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] : Set (H.edgeSet → Bool) :=
  avoidAll (fun f : F.Copy H => fixedBits (copyHostEdges f) false)

theorem noRedCopies_free {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (ω : H.edgeSet → Bool)
    (hω : ω ∈ noRedCopies F H) : ¬F.IsContained (edgeColorClass H ω false) := by
  apply edgeColorClass_free_of_no_monochrome F H ω false
  exact hω

/-- Avoiding all red copies by the local lemma retains an explicit bound
on every all-blue coordinate event. -/
theorem biased_copy_avoidance {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (D : ℕ) (hD : ∀ w, H.degree w ≤ D)
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * F.edgeFinset.card / 2) ≤ 1 / 2)
    (hincidence : (Fintype.card V * D ^ (2 * (Fintype.card V - 1)) : ℝ) *
      Real.exp (-p * F.edgeFinset.card / 2) ≤ q) :
    0 < (bitProductMeasure H.edgeSet p hp₀ hp₁).real (noRedCopies F H) ∧
      ∀ S : Finset H.edgeSet,
        (bitProductMeasure H.edgeSet p hp₀ hp₁).real (fixedBits S true ∩ noRedCopies F H) /
          (bitProductMeasure H.edgeSet p hp₀ hp₁).real (noRedCopies F H) ≤
            p ^ S.card * Real.exp (2 * (q * S.card)) := by
  classical
  let x := Real.exp (-p * F.edgeFinset.card / 2)
  let A : F.Copy H → Set (H.edgeSet → Bool) := fun f => fixedBits (copyHostEdges f) false
  let supports : F.Copy H → Finset H.edgeSet := copyHostEdges
  have hweights : ∀ e : H.edgeSet,
      ∑ f ∈ Finset.univ.filter (fun f => e ∈ supports f), x ≤ q := by
    intro e
    have hcount : (((Finset.univ : Finset (F.Copy H)).filter
        (fun f => e ∈ copyHostEdges f)).card : ℝ) ≤
          (Fintype.card V * D ^ (2 * (Fintype.card V - 1)) : ℝ) := by
      exact_mod_cast copy_edge_incidence_bound F H hF D hD e
    simpa only [Finset.sum_const, nsmul_eq_mul, supports] using
      (mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le).trans hincidence
  have hprob : ∀ f : F.Copy H,
      (bitProductMeasure H.edgeSet p hp₀ hp₁).real (A f) ≤
        x * Real.exp (-2 * (q * (supports f).card)) := by
    intro f
    change (bitProductMeasure H.edgeSet p hp₀ hp₁).real (fixedBits (copyHostEdges f) false) ≤ _
    rw [bitProductMeasure_fixedBits, copyHostEdges_card F f]
    change (1 - p) ^ F.edgeFinset.card ≤ _
    simpa only [supports, copyHostEdges_card F f, x] using
      unmarked_probability_lll_bound p q hp₁ hq F.edgeFinset.card
  have h := coordinate_lll_from_exp_bounds_fintype
    (fun _ : H.edgeSet => bernoulliMarginal p hp₀ hp₁) A supports
    (fun f => fixedBits_depends (copyHostEdges f) false) (fun _ => x) q
    (fun _ => (Real.exp_pos _).le) (fun _ => hhalf) hweights hprob
  refine ⟨h.1, ?_⟩
  intro S
  have hblue := h.2 (fixedBits S true) S (fixedBits_depends S true)
  change (bitProductMeasure H.edgeSet p hp₀ hp₁).real
      (fixedBits S true ∩ noRedCopies F H) /
      (bitProductMeasure H.edgeSet p hp₀ hp₁).real (noRedCopies F H) ≤
        (bitProductMeasure H.edgeSet p hp₀ hp₁).real (fixedBits S true) *
          Real.exp (2 * (q * S.card)) at hblue
  simpa only [bitProductMeasure_fixedBits, bernoulliWeight, ite_true] using hblue

end Erdos911
