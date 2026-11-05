import Erdos911.BiasedCopyAvoidance
import Erdos911.ConditionalFirstMoment

open MeasureTheory

namespace Erdos911

noncomputable def retainedEdges {W : Type*} [Fintype W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (E : Finset (Sym2 W)) : Finset J.edgeSet := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ E)

theorem mem_retainedEdges {W : Type*} [Fintype W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (E : Finset (Sym2 W)) (e : J.edgeSet) :
    e ∈ retainedEdges J E ↔ e.val ∈ E := by
  classical
  simp only [retainedEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem blue_copy_retained_bits {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel J.Adj]
    (ω : J.edgeSet → Bool) (f : G.Copy (H \ edgeColorClass J ω false)) :
    ∀ e ∈ retainedEdges J (copyRawEdges
      ((SimpleGraph.Copy.ofLE _ H sdiff_le).comp f)), ω e = true := by
  classical
  intro e he
  have hecopy := (mem_retainedEdges J _ e).mp he
  rw [copyRawEdges_ofLE_comp] at hecopy
  have heblue := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e.val).mp hecopy)
  rw [SimpleGraph.edgeSet_sdiff] at heblue
  have hnot : ω e ≠ false := by
    intro hfalse
    exact heblue.2 ((edgeColorClass_edge_iff J ω false e).mpr hfalse)
  cases hval : ω e <;> simp_all

/-- The biased local-lemma coloring criterion after a deterministic
subgraph reduction. The blue union bound uses full target images. -/
theorem biased_subgraph_avoiding_coloring {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph U) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (hFG : F.IsContained G) (hF : F.Connected)
    (D : ℕ) (hD : ∀ w, J.degree w ≤ D)
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * F.edgeFinset.card / 2) ≤ 1 / 2)
    (hincidence : (Fintype.card U * D ^ (2 * (Fintype.card U - 1)) : ℝ) *
      Real.exp (-p * F.edgeFinset.card / 2) ≤ q)
    (t : ℕ) (hretain : ∀ f : G.Copy H, t ≤ (retainedEdges J (copyRawEdges f)).card)
    (hbase : p * Real.exp (2 * q) ≤ 1)
    (hbudget : (H.copyCount G : ℝ) * (p * Real.exp (2 * q)) ^ t < 1) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  let μ := bitProductMeasure J.edgeSet p hp₀ hp₁
  let images : Finset (Finset (Sym2 W)) :=
    (Finset.univ : Finset (G.Copy H)).image copyRawEdges
  let B : images → Set (J.edgeSet → Bool) := fun E => fixedBits (retainedEdges J E.val) true
  have hbasenonneg : 0 ≤ p * Real.exp (2 * q) := mul_nonneg hp₀ (Real.exp_pos _).le
  obtain ⟨hpositive, hconditional⟩ := biased_copy_avoidance F J hF D hD p q hp₀ hp₁ hq hhalf hincidence
  have hB : ∀ E : images, μ.real (B E ∩ noRedCopies F J) / μ.real (noRedCopies F J) ≤
      (p * Real.exp (2 * q)) ^ t := by
    intro E
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp E.property
    have hsize : t ≤ (retainedEdges J E.val).card := by
      rw [← hf]
      exact hretain f
    have hcond := hconditional (retainedEdges J E.val)
    rw [marked_probability_exponential_factor] at hcond
    exact hcond.trans (pow_le_pow_of_le_one hbasenonneg hbase hsize)
  have himages : (Fintype.card images : ℝ) ≤ H.copyCount G := by
    rw [Fintype.card_coe]
    exact_mod_cast copyRawEdges_image_card_le G H
  have hbudget' : (Fintype.card images : ℝ) * (p * Real.exp (2 * q)) ^ t < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right himages (pow_nonneg hbasenonneg t)) hbudget
  obtain ⟨ω, hω, hnotblue⟩ := exists_avoiding_inside_event μ (noRedCopies F J) hpositive B
    ((p * Real.exp (2 * q)) ^ t) hB hbudget'
  let R := edgeColorClass J ω false
  refine ⟨R, (edgeColorClass_le J ω false).trans hJ, ?_, ?_⟩
  · intro hG
    exact noRedCopies_free F J ω hω (hFG.trans hG)
  · rintro ⟨f⟩
    let fH : G.Copy H := (SimpleGraph.Copy.ofLE _ H sdiff_le).comp f
    have hE : copyRawEdges fH ∈ images := Finset.mem_image.mpr ⟨fH, Finset.mem_univ _, rfl⟩
    exact hnotblue ⟨copyRawEdges fH, hE⟩ (blue_copy_retained_bits G H J ω f)

end Erdos911
