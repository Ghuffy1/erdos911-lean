import Erdos911.WeightedEdgeAssignment
import Erdos911.CopyImages
import Erdos911.RestrictedStarDescriptions

namespace Erdos911

theorem injective_incidence_overlap_two {I W : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq W]
    (f : I → W) (hf : Function.Injective f) (R : I → Finset (Sym2 W))
    (hincident : ∀ i e, e ∈ R i → f i ∈ e) (e : Sym2 W) :
    ((Finset.univ : Finset I).filter (fun i => e ∈ R i)).card ≤ 2 := by
  let S := (Finset.univ : Finset I).filter (fun i => e ∈ R i)
  have hsub : S.image f ⊆ e.toFinset := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact Sym2.mem_toFinset.mpr (hincident i e (Finset.mem_filter.mp hi).2)
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injective S hf).symm
    _ ≤ e.toFinset.card := Finset.card_le_card hsub
    _ ≤ 2 := by rw [Sym2.card_toFinset]; split <;> norm_num

/-- A restricted-star description for an injectively indexed edge image. -/
theorem finite_edge_star_description {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (index : V → W) (hindex : Function.Injective index)
    (F U : Finset (Sym2 W)) (m : V → ℕ) (A R : V → Finset (Sym2 W))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hU : F ⊆ U) (hR : ∀ v, R v ⊆ F)
    (hA : ∀ v, R v ⊆ A v)
    (hincident : ∀ v e, e ∈ R v → index v ∈ e)
    (hcoverage : ∀ v, (m v : ℝ) * w v ≤ 2 * (R v).card * w v) :
    ∃ (b : ℕ) (t : V → ℕ), F.card = b + ∑ v, t v ∧
      F ∈ restrictedStarSubsets U A b t ∧
      (∀ v, t v ≤ (R v).card) ∧
      (∑ v, (m v : ℝ) * w v) ≤ 4 * ∑ v, (t v : ℝ) * w v := by
  classical
  have hoverlap := injective_incidence_overlap_two index hindex R hincident
  obtain ⟨D, hDR, hdisjoint, _, hweight⟩ := exists_weighted_disjoint_assignment R w 2 hw hoverlap
  have hDF : ∀ v, D v ⊆ F := fun v => (hDR v).trans (hR v)
  have hDA : ∀ v, D v ⊆ A v := fun v => (hDR v).trans (hA v)
  obtain ⟨hmem, hcard⟩ := disjoint_assignment_reconstruction F A D hDF hDA hdisjoint
  refine ⟨F.card - ∑ v, (D v).card, fun v => (D v).card, hcard, ?_, ?_, ?_⟩
  · obtain ⟨R₀, D₀, hR₀, hRcard, hD₀, heq⟩ :=
      (mem_restrictedStarSubsets F A _ _ F).mp hmem
    exact (mem_restrictedStarSubsets U A _ _ F).mpr
      ⟨R₀, D₀, hR₀.trans hU, hRcard, hD₀, heq⟩
  · intro v
    exact Finset.card_le_card (hDR v)
  · have hclaimed : (∑ v, (m v : ℝ) * w v) ≤
        2 * ∑ v, ((R v).card : ℝ) * w v := by
      calc
        (∑ v, (m v : ℝ) * w v) ≤ ∑ v, (2 * (R v).card : ℝ) * w v :=
          Finset.sum_le_sum (fun v _ => hcoverage v)
        _ = 2 * ∑ v, ((R v).card : ℝ) * w v := by rw [Finset.mul_sum]; congr 1; ext v; ring
    norm_num only [Nat.cast_ofNat] at hweight
    linarith

theorem copy_restricted_star_description {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (f : G.Copy H) (U : Finset (Sym2 W)) (A R : V → Finset (Sym2 W))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hU : copyRawEdges f ⊆ U) (hR : ∀ v, R v ⊆ copyRawEdges f)
    (hA : ∀ v, R v ⊆ A v) (hincident : ∀ v e, e ∈ R v → f v ∈ e)
    (hcoverage : ∀ v, (G.degree v : ℝ) * w v ≤ 2 * (R v).card * w v) :
    ∃ (b : ℕ) (t : V → ℕ), G.edgeSet.ncard = b + ∑ v, t v ∧
      copyRawEdges f ∈ restrictedStarSubsets U A b t ∧
      (∀ v, t v ≤ (R v).card) ∧
      (∑ v, (G.degree v : ℝ) * w v) ≤ 4 * ∑ v, (t v : ℝ) * w v := by
  have hf : Function.Injective (f : V → W) := f.injective
  simpa only [copyRawEdges_card] using finite_edge_star_description (f : V → W) hf
    (copyRawEdges f) U (fun v => G.degree v) A R w hw hU hR hA hincident hcoverage

/-- A degree-weighted logarithmic deficit in a copy supplies a bounded
restricted-star description with one quarter of that deficit. -/
theorem finite_edges_mem_restrictedStarDescriptions {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (index : V → W) (hindex : Function.Injective index)
    (F U : Finset (Sym2 W)) (m : V → ℕ) (A R : V → Finset (Sym2 W))
    (C : V → ℕ) (D P : ℕ) (L : ℝ)
    (hC : ∀ v, 0 < C v ∧ C v ≤ P)
    (hU : F ⊆ U) (hR : ∀ v, R v ⊆ F)
    (hA : ∀ v, R v ⊆ A v) (hincident : ∀ v e, e ∈ R v → index v ∈ e)
    (hRcard : ∀ v, (R v).card ≤ D)
    (hcoverage : ∀ v, (m v : ℝ) * Real.log ((P : ℝ) / C v) ≤
      2 * (R v).card * Real.log ((P : ℝ) / C v))
    (hdeficit : 4 * L ≤ ∑ v, (m v : ℝ) * Real.log ((P : ℝ) / C v)) :
    F ∈ restrictedStarDescriptions U A C F.card D P L := by
  let w := fun v => Real.log ((P : ℝ) / C v)
  have hw : ∀ v, 0 ≤ w v := by
    intro v
    apply Real.log_nonneg
    apply (le_div_iff₀ (by exact_mod_cast (hC v).1 : (0 : ℝ) < C v)).mpr
    simpa only [one_mul] using (show (C v : ℝ) ≤ P by exact_mod_cast (hC v).2)
  obtain ⟨b, t, hcount, hmem, ht, hweight⟩ :=
    finite_edge_star_description index hindex F U m A R w hw hU hR hA hincident hcoverage
  have hsum : (∑ v, t v) ≤ F.card := by omega
  have hb : b = F.card - ∑ v, t v := by omega
  have hmass : L ≤ ∑ v, (t v : ℝ) * Real.log ((P : ℝ) / C v) := by
    dsimp only [w] at hweight
    linarith
  apply (mem_restrictedStarDescriptions U A C F.card D P L F).mpr
  refine ⟨t, fun v => (ht v).trans (hRcard v), hsum, hmass, ?_⟩
  rw [← hb]
  exact hmem

theorem copy_mem_restrictedStarDescriptions {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (f : G.Copy H) (U : Finset (Sym2 W)) (A R : V → Finset (Sym2 W))
    (C : V → ℕ) (D P : ℕ) (L : ℝ)
    (hC : ∀ v, 0 < C v ∧ C v ≤ P)
    (hU : copyRawEdges f ⊆ U) (hR : ∀ v, R v ⊆ copyRawEdges f)
    (hA : ∀ v, R v ⊆ A v) (hincident : ∀ v e, e ∈ R v → f v ∈ e)
    (hRcard : ∀ v, (R v).card ≤ D)
    (hcoverage : ∀ v, (G.degree v : ℝ) * Real.log ((P : ℝ) / C v) ≤
      2 * (R v).card * Real.log ((P : ℝ) / C v))
    (hdeficit : 4 * L ≤ ∑ v, (G.degree v : ℝ) * Real.log ((P : ℝ) / C v)) :
    copyRawEdges f ∈ restrictedStarDescriptions U A C G.edgeSet.ncard D P L := by
  have hf : Function.Injective (f : V → W) := f.injective
  simpa only [copyRawEdges_card] using finite_edges_mem_restrictedStarDescriptions
    (f : V → W) hf (copyRawEdges f) U (fun v => G.degree v) A R C D P L hC hU hR hA
    hincident hRcard hcoverage hdeficit

end Erdos911
