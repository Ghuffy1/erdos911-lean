import Erdos911.PairMarkedRows
import Erdos911.PairCopyAvoidance

open MeasureTheory

namespace Erdos911

noncomputable def pairBadRows {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (d : ℕ) (ω : Sym2 L → Bool) : Finset R := by
  classical
  exact Finset.univ.filter (fun y => d ≤ 2 * (pairBlueRow (N y) ω).card)

/-- Choose one marking which avoids all red pair-pattern copies and has
few high-blue-degree rows. No independence is assumed after conditioning. -/
theorem exists_pair_marking_with_few_bad_rows {V L R : Type*}
    [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] [Fintype R]
    (F : SimpleGraph V) [DecidableRel F.Adj] (U : SimpleGraph L) [DecidableRel U.Adj]
    (hF : F.Connected) (D : ℕ) (hD : ∀ x, U.degree x ≤ D)
    (N : R → Finset L) (d a : ℕ) (hd : 4 ≤ d)
    (hsize : ∀ y, (N y).sym2.card ≤ a * (d / 4))
    (ρ η : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hη : 0 ≤ η) (hsmall : 4 * η ≤ ρ)
    (hhalf : Real.exp (-ρ * F.edgeSet.ncard / 2) ≤ 1 / 2)
    (hbudget : (Fintype.card V * D ^ (2 * (Fintype.card V - 1)) : ℕ) *
      Real.exp (-ρ * F.edgeSet.ncard / 2) ≤ η)
    (hcorrection : ∀ y, Real.exp (2 * (η * (N y).sym2.card)) ≤ 2) :
    ∃ ω : Sym2 L → Bool,
      (∀ f : F.Copy U, ω ∉ fixedBits (copyRawEdges f) false) ∧
      ((pairBadRows N d ω).card : ℝ) ≤
        2 * (((a : ℝ) * Real.exp 1 * ρ) ^ (d / 4)) * Fintype.card R := by
  classical
  let μ := bitProductMeasure (Sym2 L) ρ hρ0 hρ1
  let A := fun f : F.Copy U => fixedBits (copyRawEdges f) false
  let Good := avoidAll A
  let B := ((a : ℝ) * Real.exp 1 * ρ) ^ (d / 4)
  obtain ⟨hGood, hconditional⟩ := connected_pair_copy_avoidance F U hF D hD ρ η hρ0 hρ1 hη
    hsmall hhalf hbudget
  have hprob (y : R) : μ.real ({ω | d ≤ 2 * (pairBlueRow (N y) ω).card} ∩ Good) / μ.real Good ≤ 2 * B := by
    have hcond := hconditional {ω | d ≤ 2 * (pairBlueRow (N y) ω).card} (N y).sym2 (pairBlueRow_depends (N y) d)
    have htail := pairBlueRow_probability (N y) d a hd (hsize y) ρ hρ0 hρ1
    have hB0 : 0 ≤ B := by dsimp only [B]; positivity
    have hprod := mul_le_mul htail (hcorrection y) (Real.exp_pos _).le hB0
    exact hcond.trans (by simpa only [B, mul_comm] using hprod)
  obtain ⟨ω, hω, hcost⟩ := exists_conditional_cost_le μ Good hGood
    (fun y : R => {ω | d ≤ 2 * (pairBlueRow (N y) ω).card})
    (fun _ => (1 : ℝ)) (fun _ => 2 * B) (fun _ => by norm_num) hprob
  have hcount : (∑ y : R,
      ({ω | d ≤ 2 * (pairBlueRow (N y) ω).card} : Set (Sym2 L → Bool)).indicator (fun _ => (1 : ℝ)) ω) =
      ((pairBadRows N d ω).card : ℝ) := by
    have hnat : (pairBadRows N d ω).card =
        ∑ y : R, if d ≤ 2 * (pairBlueRow (N y) ω).card then (1 : ℕ) else 0 := by
      rw [pairBadRows, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hnat, Nat.cast_sum]
    simp only [Set.indicator, Set.mem_ofPred_eq, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hcost' : ((pairBadRows N d ω).card : ℝ) ≤ 2 * B * Fintype.card R := by
    rw [hcount] at hcost
    simpa [mul_comm] using hcost
  exact ⟨ω, hω, hcost'⟩

end Erdos911
