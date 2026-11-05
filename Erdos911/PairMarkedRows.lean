import Erdos911.BinomialMarkTail
import Erdos911.IncidenceGraph
import Mathlib.Data.Finset.Sym

open MeasureTheory

namespace Erdos911

/-- A marked unordered pair makes both of its endpoints blue in every
row containing that pair. Diagonal pairs are harmlessly included. -/
noncomputable def pairBlueRow {L : Type*} [DecidableEq L] (S : Finset L) (ω : Sym2 L → Bool) : Finset L :=
  (markedElements S.sym2 ω).biUnion Sym2.toFinset

noncomputable def pairRedRow {L : Type*} [DecidableEq L] (S : Finset L) (ω : Sym2 L → Bool) : Finset L :=
  S \ pairBlueRow S ω

theorem pairBlueRow_subset {L : Type*} [DecidableEq L] (S : Finset L) (ω : Sym2 L → Bool) :
    pairBlueRow S ω ⊆ S := by
  classical
  intro x hx
  obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
  have heS : e ∈ S.sym2 := (Finset.mem_filter.mp he).1
  exact Finset.mem_sym2_iff.mp heS x (Sym2.mem_toFinset.mp hx)

theorem pairBlueRow_card_le {L : Type*} [DecidableEq L] (S : Finset L) (ω : Sym2 L → Bool) :
    (pairBlueRow S ω).card ≤ 2 * (markedElements S.sym2 ω).card := by
  classical
  calc
    _ ≤ ∑ e ∈ markedElements S.sym2 ω, e.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ markedElements S.sym2 ω, 2 := by
      apply Finset.sum_le_sum
      intro e _
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    _ = _ := by simp [mul_comm]

theorem marked_pair_endpoints_blue {L : Type*} [DecidableEq L]
    (S : Finset L) (ω : Sym2 L → Bool) (x z : L) (hx : x ∈ S) (hz : z ∈ S)
    (hmark : ω s(x, z) = true) : x ∈ pairBlueRow S ω ∧ z ∈ pairBlueRow S ω := by
  classical
  have hp : s(x, z) ∈ markedElements S.sym2 ω := Finset.mem_filter.mpr
    ⟨Finset.mk_mem_sym2_iff.mpr ⟨hx, hz⟩, hmark⟩
  constructor
  · exact Finset.mem_biUnion.mpr ⟨s(x, z), hp, by simp⟩
  · exact Finset.mem_biUnion.mpr ⟨s(x, z), hp, by simp⟩

theorem red_row_pair_unmarked {L : Type*} [DecidableEq L]
    (S : Finset L) (ω : Sym2 L → Bool) (x z : L)
    (hx : x ∈ pairRedRow S ω) (hz : z ∈ pairRedRow S ω) : ω s(x, z) = false := by
  classical
  have hx' := Finset.mem_sdiff.mp hx
  have hz' := Finset.mem_sdiff.mp hz
  cases hw : ω s(x, z) with
  | false => rfl
  | true => exact (hx'.2 (marked_pair_endpoints_blue S ω x z hx'.1 hz'.1 hw).1).elim

theorem row_pair_count_le_square {L : Type*} [DecidableEq L] (S : Finset L) : S.sym2.card ≤ S.card ^ 2 := by
  rw [Finset.sym2_eq_image]
  exact (Finset.card_image_le).trans (by simp [pow_two])

theorem pairBlueRow_depends {L : Type*} [DecidableEq L]
    (S : Finset L) (d : ℕ) : DependsOnlyOn {ω | d ≤ 2 * (pairBlueRow S ω).card} S.sym2 := by
  classical
  intro ω ω' heq hω
  have hmarks : markedElements S.sym2 ω = markedElements S.sym2 ω' := by
    apply Finset.ext
    intro e
    simp only [markedElements, Finset.mem_filter]
    constructor <;> rintro ⟨he, hmark⟩
    · exact ⟨he, by rw [← heq e he]; exact hmark⟩
    · exact ⟨he, by rw [heq e he]; exact hmark⟩
  change d ≤ 2 * (pairBlueRow S ω).card at hω
  change d ≤ 2 * (pairBlueRow S ω').card
  have hblue : pairBlueRow S ω = pairBlueRow S ω' := by unfold pairBlueRow; rw [hmarks]
  rw [← hblue]
  exact hω

/-- A high-blue-degree row requires at least floor(d/4) independently
marked pair variables. -/
theorem pairBlueRow_probability {L : Type*} [DecidableEq L] [Fintype L]
    (S : Finset L) (d a : ℕ) (hd : 4 ≤ d) (hsize : S.sym2.card ≤ a * (d / 4))
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (bitProductMeasure (Sym2 L) ρ hρ0 hρ1).real {ω | d ≤ 2 * (pairBlueRow S ω).card} ≤
      ((a : ℝ) * Real.exp 1 * ρ) ^ (d / 4) := by
  have hsub : {ω : Sym2 L → Bool | d ≤ 2 * (pairBlueRow S ω).card} ⊆
      {ω | d / 4 ≤ (markedElements S.sym2 ω).card} := by
    intro ω hω
    change d ≤ 2 * (pairBlueRow S ω).card at hω
    change d / 4 ≤ (markedElements S.sym2 ω).card
    have hcard := pairBlueRow_card_le S ω
    omega
  exact (measureReal_mono hsub).trans (marked_elements_tail_ratio S.sym2 (d / 4) a (by omega) hsize ρ hρ0 hρ1)

end Erdos911
