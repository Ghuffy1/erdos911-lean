import Erdos911.HeavyRowPacking
import Erdos911.FiberPruning

namespace Erdos911

/-- The heavy-pair extraction remains valid after small right fibers
are removed. Its loss depends on the number of left vertices, not on
the number or diversity of neighborhood patterns. -/
theorem exists_large_heavy_row_packing {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] [Nonempty L]
    (S : R → Finset L) (W : ℝ) (q D t : ℕ)
    (hdegree : letI : DecidableRel (heavyIncidenceGraph S W).Adj := Classical.decRel _
      ∀ x, (heavyIncidenceGraph S W).degree x ≤ D)
    (hmany : Fintype.card R ≤ 2 * (heavyConcentratedRows S W q).card) :
    ∃ (U : Finset R) (f : R → L) (N : R → Finset L),
      Fintype.card R ≤ 2 * (D * (D + 1) + 1) * (U.card + t * Fintype.card L) ∧
      (∀ y, N y ⊆ S y) ∧
      (∀ y ∈ U, (N y).card = q ∧ N y ⊆ heavyIncidenceBall S W (f y)) ∧
      (∀ y ∉ U, N y = ∅) ∧
      (∀ y ∈ U, t ≤ (U.filter (fun z => f z = f y)).card) ∧
      (∀ y ∈ U, ∀ z ∈ U, f y ≠ f z →
        Disjoint (heavyIncidenceBall S W (f y)) (heavyIncidenceBall S W (f z))) ∧
      (∀ x, (heavyIncidenceBall S W x).card ≤ D + 1) := by
  classical
  obtain ⟨U₀, f, N₀, hmass, hsub, hrow, hzero, hdisjoint, hball⟩ :=
    exists_heavy_row_packing S W q D hdegree
  let U := largeFiberRows U₀ f t
  let N : R → Finset L := fun y => if y ∈ U then N₀ y else ∅
  have hUU : U ⊆ U₀ := largeFiberRows_subset U₀ f t
  have hcard := largeFiberRows_card_bound U₀ f t
  refine ⟨U, f, N, ?_, ?_, ?_, ?_, ?_, ?_, hball⟩
  · have h₁ := hmany.trans (Nat.mul_le_mul_left 2 hmass)
    have h₂ := Nat.mul_le_mul_left (2 * (D * (D + 1) + 1)) hcard
    have h₁' : Fintype.card R ≤ 2 * (D * (D + 1) + 1) * U₀.card := by
      simpa only [Nat.mul_assoc] using h₁
    exact h₁'.trans h₂
  · intro y
    by_cases hy : y ∈ U
    · simpa only [N, hy, ite_true] using hsub y
    · simp only [N, hy, ite_false, Finset.empty_subset]
  · intro y hy
    simpa only [N, hy, ite_true] using hrow y (hUU hy)
  · intro y hy
    simp only [N, hy, ite_false]
  · exact fun y hy => largeFiberRows_minimum U₀ f t y hy
  · exact fun y hy z hz => hdisjoint y (hUU hy) z (hUU hz)

/-- If the discarded-fiber allowance is at most one quarter of the
right mass, the retained rows carry the stated fixed fraction. -/
theorem large_heavy_row_mass (b a m t u : ℕ)
    (hmass : b ≤ 2 * m * (u + t * a)) (hsmall : 4 * m * t * a ≤ b) :
    b ≤ 4 * m * u := by
  nlinarith only [hmass, hsmall]

end Erdos911
