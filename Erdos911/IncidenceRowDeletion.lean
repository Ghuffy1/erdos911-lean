import Erdos911.IncidencePairWeights

namespace Erdos911

noncomputable def deletedIncidenceRows {L R : Type*} [DecidableEq L] [DecidableEq R]
    (S : R → Finset L) (badL : Finset L) (badR badRows : Finset R) (y : R) : Finset L :=
  if y ∈ badR ∨ y ∈ badRows then ∅ else S y \ badL

theorem incidence_deleted_left_mass {L R : Type*} [Fintype L] [DecidableEq L] [Fintype R]
    (S : R → Finset L) (badL : Finset L) :
    (∑ y : R, (S y ∩ badL).card) = ∑ x ∈ badL, (incidenceColumn S x).card := by
  classical
  have hsum := sum_incidenceColumn_card (fun y => S y ∩ badL)
  have hcol (x : L) : (incidenceColumn (fun y => S y ∩ badL) x).card =
      if x ∈ badL then (incidenceColumn S x).card else 0 := by
    by_cases hx : x ∈ badL
    · have heq : incidenceColumn (fun y => S y ∩ badL) x = incidenceColumn S x := by
        apply Finset.ext
        intro y
        simp only [incidenceColumn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, hx, and_true]
      rw [heq, ite_eq_left hx]
    · have heq : incidenceColumn (fun y => S y ∩ badL) x = ∅ := by
        apply Finset.ext
        intro y
        simp only [incidenceColumn, Finset.mem_filter, Finset.mem_univ, Finset.mem_inter, hx, and_false, Finset.notMem_empty]
      rw [heq, Finset.card_empty, ite_eq_right hx]
  simp_rw [hcol] at hsum
  rw [← Finset.sum_filter] at hsum
  have hf : (Finset.univ : Finset L).filter (fun x => x ∈ badL) = badL := by ext x; simp
  rw [hf] at hsum
  exact hsum.symm

/-- Deleting left roles and two classes of right roles has the expected
sum-of-degrees charge, with overlaps counted only in the upper bound. -/
theorem incidence_row_deletion_bound {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (S : R → Finset L) (badL : Finset L) (badR badRows : Finset R) (d : ℕ)
    (hrow : ∀ y, (S y).card = d) :
    (∑ y : R, (S y).card) ≤
      (∑ y : R, (deletedIncidenceRows S badL badR badRows y).card) +
        (∑ x ∈ badL, (incidenceColumn S x).card) + d * badR.card + d * badRows.card := by
  have hpoint (y : R) : (S y).card ≤ (deletedIncidenceRows S badL badR badRows y).card +
      (S y ∩ badL).card + (if y ∈ badR then d else 0) + (if y ∈ badRows then d else 0) := by
    have hsplit := Finset.card_sdiff_add_card_inter (S y) badL
    by_cases hR : y ∈ badR <;> by_cases hB : y ∈ badRows
    · simp only [deletedIncidenceRows, hR, true_or, ite_true, Finset.card_empty, hB]
      have hs := hrow y
      omega
    · simp only [deletedIncidenceRows, hR, true_or, ite_true, Finset.card_empty, hB, ite_false]
      have hs := hrow y
      omega
    · simp only [deletedIncidenceRows, hR, false_or, hB, ite_true, Finset.card_empty, ite_false]
      have hs := hrow y
      omega
    · simp only [deletedIncidenceRows, hR, hB, false_or, ite_false]
      omega
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset R)) => hpoint y)
  simp only [Finset.sum_add_distrib] at hsum
  rw [incidence_deleted_left_mass] at hsum
  have hRsum : (∑ y : R, if y ∈ badR then d else 0) = d * badR.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hBsum : (∑ y : R, if y ∈ badRows then d else 0) = d * badRows.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hRsum, hBsum] at hsum
  exact hsum

end Erdos911
