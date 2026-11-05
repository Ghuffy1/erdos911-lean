import Erdos911.TargetBlockTests
import Erdos911.IncidenceRowDeletion

namespace Erdos911

/-- Removing target left vertices of degree at most D costs at most
D times the full left order, uniformly over all right rows. -/
theorem target_truncation_mass {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (D : ℕ) :
    (∑ y : R, (N y).card) ≤ (∑ y : R, (targetTruncatedRows N D y).card) + Fintype.card A * D := by
  classical
  let H := targetHighLeft N D
  let L := (Finset.univ : Finset A) \ H
  have hlow (x : A) (hx : x ∈ L) : (incidenceColumn N x).card ≤ D := by
    have hn := (Finset.mem_sdiff.mp hx).2
    have hh : ¬D < (incidenceColumn N x).card := by
      intro hh
      exact hn ((mem_targetHighLeft N D x).mpr hh)
    omega
  have hleft : (∑ x ∈ L, (incidenceColumn N x).card) ≤ Fintype.card A * D := by
    calc
      _ ≤ ∑ _x ∈ L, D := Finset.sum_le_sum hlow
      _ = L.card * D := by simp
      _ ≤ _ := Nat.mul_le_mul_right D (Finset.card_le_univ _)
  have hpoint (y : R) : (N y).card = (targetTruncatedRows N D y).card + (N y ∩ L).card := by
    have heq : N y ∩ L = N y \ H := by
      ext x
      simp only [L, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    rw [heq]
    have hh := Finset.card_sdiff_add_card_inter (N y) H
    change (N y).card = (N y ∩ H).card + (N y \ H).card
    omega
  have hsum : (∑ y : R, (N y).card) = (∑ y : R, (targetTruncatedRows N D y).card) +
      ∑ x ∈ L, (incidenceColumn N x).card := by
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, incidence_deleted_left_mass]
  omega

theorem substantial_target_rows_large {A R : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    (N : R → Finset A) (q D : ℕ) (hq : 0 < q) (hrow : ∀ y, (N y).card = q)
    (hlarge : 16 * Fintype.card A * D ≤ q * Fintype.card R) :
    7 * Fintype.card R ≤ 8 * (substantialTargetRows (targetTruncatedRows N D) (q / 2)).card := by
  classical
  let T := targetTruncatedRows N D
  let B := substantialTargetRows T (q / 2)
  let bad := (Finset.univ : Finset R) \ B
  have hmax (y : R) : (T y).card ≤ (N y).card := Finset.card_le_card (targetTruncatedRows_subset N D y)
  have hpoint (y : R) : (if y ∈ bad then q else 0) + 2 * (T y).card ≤ 2 * (N y).card := by
    by_cases hy : y ∈ bad
    · have hn := (Finset.mem_sdiff.mp hy).2
      have hsmall : (T y).card < q / 2 := by
        by_contra hh
        exact hn ((mem_substantialTargetRows T (q / 2) y).mpr (by omega))
      simp only [hy, ite_true, hrow]
      omega
    · simp only [hy, ite_false, zero_add]
      exact Nat.mul_le_mul_left 2 (hmax y)
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset R)) => hpoint y)
  have hqsum : (∑ y : R, if y ∈ bad then q else 0) = q * bad.card := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hqsum] at hsum
  have hmass := target_truncation_mass N D
  have hloss : q * bad.card ≤ 2 * Fintype.card A * D := by
    change (∑ y : R, (N y).card) ≤ (∑ y : R, (T y).card) + Fintype.card A * D at hmass
    nlinarith only [hsum, hmass]
  have hbad : 8 * bad.card ≤ Fintype.card R := by
    apply Nat.le_of_mul_le_mul_left (c := q) _ hq
    nlinarith only [hloss, hlarge]
  have hpartition := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  rw [Finset.card_univ] at hpartition
  change bad.card + B.card = Fintype.card R at hpartition
  change 7 * Fintype.card R ≤ 8 * B.card
  omega

end Erdos911
