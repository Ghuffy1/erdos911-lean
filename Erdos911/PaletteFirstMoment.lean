import Erdos911.PaletteRedSupport
import Erdos911.BlueComponentProbability
import Erdos911.ComponentStatistics
import Erdos911.ConditionalMarkBudget

open MeasureTheory

namespace Erdos911

noncomputable def paletteBadEdgeMass {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ t : G.ConnectedComponent, Fintype t.supp]
    (d : ℕ) (ω : Sym2 A → Bool) : ℝ := by
  classical
  exact ∑ c ∈ (Finset.univ : Finset G.ConnectedComponent).filter
    (fun c => ω ∈ paletteComponentBad (G.induce c.supp) d), ((G.induce c.supp).edgeSet.ncard : ℝ)

theorem paletteBadEdgeMass_nonneg {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ t : G.ConnectedComponent, Fintype t.supp]
    (d : ℕ) (ω : Sym2 A → Bool) : 0 ≤ paletteBadEdgeMass G d ω := by
  classical
  exact Finset.sum_nonneg (fun c _ => Nat.cast_nonneg _)

set_option linter.deprecated false in
/-- One palette has both small red-copy support and small bad-component
edge mass whenever their combined first-moment budget is small enough. -/
theorem exists_palette_with_small_costs {V U W A : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    [Fintype A] [DecidableEq A]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ t : G.ConnectedComponent, Fintype t.supp]
    (F : SimpleGraph U) (H : SimpleGraph W) (c : W → A)
    (d : ℕ) (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hred : ∀ e : H.edgeSet, (bitProductMeasure (Sym2 A) p hp0 hp1).real
      {ω | e ∈ paletteRedSupport F H c ω} ≤ q)
    (hbad : ∀ t : G.ConnectedComponent, (bitProductMeasure (Sym2 A) p hp0 hp1).real
      (paletteComponentBad (G.induce t.supp) d) ≤ 1 / 1000)
    (hbudget : 64 * q * H.edgeSet.ncard + (4 / 1000 : ℝ) * G.edgeSet.ncard ≤ G.edgeSet.ncard) :
    ∃ ω : Sym2 A → Bool,
      ((paletteRedSupport F H c ω).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 64 ∧
      paletteBadEdgeMass G d ω ≤ (G.edgeSet.ncard : ℝ) / 4 := by
  classical
  let μ := bitProductMeasure (Sym2 A) p hp0 hp1
  let events : H.edgeSet ⊕ G.ConnectedComponent → Set (Sym2 A → Bool) := Sum.elim
    (fun e => {ω | e ∈ paletteRedSupport F H c ω})
    (fun t => paletteComponentBad (G.induce t.supp) d)
  let costs : H.edgeSet ⊕ G.ConnectedComponent → ℝ := Sum.elim (fun _ => 64)
    (fun t => 4 * (G.induce t.supp).edgeSet.ncard)
  let bounds : H.edgeSet ⊕ G.ConnectedComponent → ℝ := Sum.elim (fun _ => q) (fun _ => 1 / 1000)
  have hcosts : ∀ i, 0 ≤ costs i := by intro i; cases i <;> dsimp [costs] <;> positivity
  have hprob : ∀ i, μ.real (events i ∩ Set.univ) / μ.real Set.univ ≤ bounds i := by
    intro i
    simp only [Set.inter_univ, probReal_univ, div_one]
    cases i with
    | inl e => exact hred e
    | inr t => exact hbad t
  obtain ⟨ω, _, hω⟩ := exists_conditional_cost_le μ Set.univ (by simp)
    events costs bounds hcosts hprob
  have htotal : (∑ t : G.ConnectedComponent, ((G.induce t.supp).edgeSet.ncard : ℝ)) =
      G.edgeSet.ncard := by exact_mod_cast component_edge_count_sum G
  have hboundSum : (∑ i : H.edgeSet ⊕ G.ConnectedComponent, bounds i * costs i) =
      64 * q * H.edgeSet.ncard + (4 / 1000 : ℝ) * G.edgeSet.ncard := by
    rw [Fintype.sum_sum_type]
    dsimp only [bounds, costs, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hs : (∑ t : G.ConnectedComponent, (1 / 1000 : ℝ) * (4 * (G.induce t.supp).edgeSet.ncard)) =
        (4 / 1000 : ℝ) * G.edgeSet.ncard := by
      rw [← htotal, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hs, Set.fintypeCard_eq_ncard]
    ring
  have hcostSum : (∑ i : H.edgeSet ⊕ G.ConnectedComponent,
      (events i).indicator (fun _ => costs i) ω) =
      64 * (paletteRedSupport F H c ω).card + 4 * paletteBadEdgeMass G d ω := by
    rw [Fintype.sum_sum_type]
    dsimp only [events, costs, Sum.elim_inl, Sum.elim_inr, Set.indicator]
    simp only [Set.mem_setOf_eq]
    have hredsum : (∑ e : H.edgeSet, if e ∈ paletteRedSupport F H c ω then (64 : ℝ) else 0) =
        64 * (paletteRedSupport F H c ω).card := by
      rw [← Finset.sum_filter]
      have hs : (Finset.univ : Finset H.edgeSet).filter (fun e => e ∈ paletteRedSupport F H c ω) =
          paletteRedSupport F H c ω := by ext e; simp
      rw [hs]
      simp [mul_comm]
    have hbadsum : (∑ t : G.ConnectedComponent,
        if ω ∈ paletteComponentBad (G.induce t.supp) d then (4 : ℝ) * (G.induce t.supp).edgeSet.ncard else 0) =
        4 * paletteBadEdgeMass G d ω := by
      rw [← Finset.sum_filter]
      exact (Finset.mul_sum ..).symm
    rw [hredsum, hbadsum]
  rw [hboundSum, hcostSum] at hω
  have hrednonneg : (0 : ℝ) ≤ (paletteRedSupport F H c ω).card := Nat.cast_nonneg _
  have hbadnonneg := paletteBadEdgeMass_nonneg G d ω
  exact ⟨ω, by constructor <;> nlinarith only [hω, hbudget, hrednonneg, hbadnonneg]⟩

end Erdos911
