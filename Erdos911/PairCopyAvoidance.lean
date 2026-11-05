import Erdos911.AnchoredCopyCounting
import Erdos911.ConditionalMarkBudget

open MeasureTheory

namespace Erdos911

theorem raw_copy_edge_incidence_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hF : F.Connected) (D : ℕ) (hD : ∀ w, H.degree w ≤ D) (e : Sym2 W) :
    ((Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyRawEdges f)).card ≤
      Fintype.card V * D ^ (2 * (Fintype.card V - 1)) := by
  classical
  by_cases he : e ∈ H.edgeSet
  · let a : H.edgeSet := ⟨e, he⟩
    have heq : (Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyRawEdges f) =
        Finset.univ.filter (fun f => a ∈ copyHostEdges f) := by
      apply Finset.ext
      intro f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_copyRawEdges_iff, mem_copyHostEdges_iff]
    rw [heq]
    exact copy_edge_incidence_bound F H hF D hD a
  · have hempty : (Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyRawEdges f) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro f hf
      have hfe := (mem_copyRawEdges_iff f e).mp (Finset.mem_filter.mp hf).2
      exact he (f.toSubgraph.edgeSet_subset hfe)
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- A product-coordinate local lemma avoiding every unmarked connected
pair-pattern copy, with a conditional bound for arbitrary local events. -/
theorem connected_pair_copy_avoidance {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hF : F.Connected) (D : ℕ) (hD : ∀ w, H.degree w ≤ D)
    (ρ η : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (_hη : 0 ≤ η) (hsmall : 4 * η ≤ ρ)
    (hhalf : Real.exp (-ρ * F.edgeSet.ncard / 2) ≤ 1 / 2)
    (hbudget : (Fintype.card V * D ^ (2 * (Fintype.card V - 1)) : ℕ) *
      Real.exp (-ρ * F.edgeSet.ncard / 2) ≤ η) :
    let μ := bitProductMeasure (Sym2 W) ρ hρ0 hρ1
    let A := fun f : F.Copy H => fixedBits (copyRawEdges f) false
    0 < μ.real (avoidAll A) ∧
      ∀ (B : Set (Sym2 W → Bool)) (S : Finset (Sym2 W)), DependsOnlyOn B S →
        μ.real (B ∩ avoidAll A) / μ.real (avoidAll A) ≤
          μ.real B * Real.exp (2 * (η * S.card)) := by
  classical
  let x := Real.exp (-ρ * F.edgeSet.ncard / 2)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hinc (e : Sym2 W) :
      (∑ f ∈ (Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyRawEdges f), x) ≤ η := by
    have hc := raw_copy_edge_incidence_bound F H hF D hD e
    have hcR : (((Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyRawEdges f)).card : ℝ) ≤
        (Fintype.card V * D ^ (2 * (Fintype.card V - 1)) : ℕ) := by exact_mod_cast hc
    have hm := mul_le_mul_of_nonneg_right hcR hx0
    simpa only [Finset.sum_const, nsmul_eq_mul] using hm.trans hbudget
  have hprob (f : F.Copy H) : (bitProductMeasure (Sym2 W) ρ hρ0 hρ1).real
      (fixedBits (copyRawEdges f) false) ≤ x * Real.exp (-2 * (η * (copyRawEdges f).card)) := by
    rw [bitProductMeasure_fixedBits, copyRawEdges_card]
    simpa only [bernoulliWeight, Bool.false_eq_true, ite_false] using
      unmarked_probability_lll_bound ρ η hρ1 hsmall F.edgeSet.ncard
  exact coordinate_lll_from_exp_bounds_fintype (fun _ : Sym2 W => bernoulliMarginal ρ hρ0 hρ1)
    (fun f : F.Copy H => fixedBits (copyRawEdges f) false) copyRawEdges
    (fun f => fixedBits_depends (copyRawEdges f) false) (fun _ => x) η
    (fun _ => hx0) (fun _ => hhalf) hinc hprob

end Erdos911
