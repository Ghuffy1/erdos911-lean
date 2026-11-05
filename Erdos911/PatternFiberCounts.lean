import Erdos911.FiberPruning

namespace Erdos911

def patternFiber {R P : Type*} [DecidableEq P] (U : Finset R) (f : R → P) (p : P) : Finset R :=
  U.filter (fun y => f y = p)

theorem sum_pattern_fiber_cards {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (C : Finset P) (hC : ∀ y ∈ U, f y ∈ C) :
    (∑ p ∈ C, (patternFiber U f p).card) = U.card := by
  classical
  simp_rw [patternFiber, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  simp [hC y hy]

noncomputable def lightPatternRows {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (b M : ℕ) : Finset R :=
  U.filter (fun y => 8 * M * (patternFiber U f (f y)).card < b)

/-- Rare patterns contain at most one eighth of the reference row count. -/
theorem lightPatternRows_card_bound {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (b M : ℕ) (hM : 0 < M) (hcount : (U.image f).card ≤ M) :
    8 * (lightPatternRows U f b M).card ≤ b := by
  classical
  let C := U.image f
  let L := lightPatternRows U f b M
  have hLU : L ⊆ U := Finset.filter_subset _ _
  have hfiber (p : P) : 8 * M * (patternFiber L f p).card ≤ b := by
    by_cases hp : (patternFiber L f p).Nonempty
    · obtain ⟨y, hy⟩ := hp
      obtain ⟨hyL, hyp⟩ := Finset.mem_filter.mp hy
      have hsmall := (Finset.mem_filter.mp hyL).2
      rw [hyp] at hsmall
      have hsub : patternFiber L f p ⊆ patternFiber U f p := Finset.filter_subset_filter _ hLU
      exact (Nat.mul_le_mul_left (8 * M) (Finset.card_le_card hsub)).trans hsmall.le
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hp, Finset.card_empty, mul_zero, Nat.zero_le]
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ C) => hfiber p)
  rw [← Finset.mul_sum, sum_pattern_fiber_cards L f C (fun y hy => Finset.mem_image_of_mem f (hLU hy))] at hsum
  have hs : 8 * M * L.card ≤ C.card * b := by simpa only [Finset.sum_const, smul_eq_mul] using hsum
  have hc : C.card * b ≤ M * b := Nat.mul_le_mul_right b hcount
  have hprod : M * (8 * L.card) ≤ M * b := by nlinarith only [hs, hc]
  exact Nat.le_of_mul_le_mul_left hprod hM

noncomputable def poorLowPatternRows {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (Low : R → Prop) [DecidablePred Low] : Finset R :=
  U.filter (fun y => 2 * ((patternFiber U f (f y)).filter Low).card < (patternFiber U f (f y)).card)

/-- A pattern with fewer than half low rows can charge all its rows to
twice its high rows. Summing the disjoint fibers preserves this bound. -/
theorem poorLowPatternRows_card_bound {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (Low : R → Prop) [DecidablePred Low] :
    (poorLowPatternRows U f Low).card ≤ 2 * (U.filter (fun y => ¬ Low y)).card := by
  classical
  let C := U.image f
  let B := poorLowPatternRows U f Low
  let H := U.filter (fun y => ¬Low y)
  have hBU : B ⊆ U := Finset.filter_subset _ _
  have hHU : H ⊆ U := Finset.filter_subset _ _
  have hfiber (p : P) : (patternFiber B f p).card ≤ 2 * (patternFiber H f p).card := by
    by_cases hp : (patternFiber B f p).Nonempty
    · obtain ⟨y, hy⟩ := hp
      obtain ⟨hyB, hyp⟩ := Finset.mem_filter.mp hy
      have hpoor := (Finset.mem_filter.mp hyB).2
      rw [hyp] at hpoor
      have hpart := Finset.card_filter_add_card_filter_not (s := patternFiber U f p) Low
      have heq : (patternFiber U f p).filter (fun y => ¬Low y) = patternFiber H f p := by
        ext z
        simp only [patternFiber, H, Finset.mem_filter]
        tauto
      rw [heq] at hpart
      have hsub : (patternFiber B f p).card ≤ (patternFiber U f p).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hBU)
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hp, Finset.card_empty, Nat.zero_le]
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ C) => hfiber p)
  rw [← Finset.mul_sum, sum_pattern_fiber_cards B f C (fun y hy => Finset.mem_image_of_mem f (hBU hy)),
    sum_pattern_fiber_cards H f C (fun y hy => Finset.mem_image_of_mem f (hHU hy))] at hsum
  exact hsum

end Erdos911
