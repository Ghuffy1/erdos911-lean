import Erdos911.HeavyIncidenceGeometry

namespace Erdos911

theorem sum_assignment_fiber_cards {R A : Type*} [DecidableEq R] [DecidableEq A] [Fintype A]
    (U : Finset R) (f : R → A) :
    (∑ a : A, (U.filter (fun y => f y = a)).card) = U.card := by
  classical
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

noncomputable def largeFiberRows {R A : Type*} [DecidableEq R] [DecidableEq A]
    (U : Finset R) (f : R → A) (t : ℕ) : Finset R := by
  classical
  exact U.filter (fun y => t ≤ (U.filter (fun z => f z = f y)).card)

theorem largeFiberRows_subset {R A : Type*} [DecidableEq R] [DecidableEq A]
    (U : Finset R) (f : R → A) (t : ℕ) : largeFiberRows U f t ⊆ U := Finset.filter_subset _ _

theorem largeFiberRows_fiber_eq {R A : Type*} [DecidableEq R] [DecidableEq A]
    (U : Finset R) (f : R → A) (t : ℕ) (a : A)
    (ha : t ≤ (U.filter (fun y => f y = a)).card) :
    (largeFiberRows U f t).filter (fun y => f y = a) = U.filter (fun y => f y = a) := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.filter_subset_filter _ (largeFiberRows_subset U f t)
  · intro y hy
    obtain ⟨hyU, hya⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hyU, ?_⟩, hya⟩
    simpa only [hya] using ha

theorem largeFiberRows_minimum {R A : Type*} [DecidableEq R] [DecidableEq A]
    (U : Finset R) (f : R → A) (t : ℕ) (y : R) (hy : y ∈ largeFiberRows U f t) :
    t ≤ ((largeFiberRows U f t).filter (fun z => f z = f y)).card := by
  have h := (Finset.mem_filter.mp hy).2
  rw [largeFiberRows_fiber_eq U f t (f y) h]
  exact h

/-- Deleting every assignment class smaller than t loses at most t
times the number of available labels. -/
theorem largeFiberRows_card_bound {R A : Type*}
    [DecidableEq R] [DecidableEq A] [Fintype A]
    (U : Finset R) (f : R → A) (t : ℕ) :
    U.card ≤ (largeFiberRows U f t).card + t * Fintype.card A := by
  classical
  have hfiber (a : A) : (U.filter (fun y => f y = a)).card ≤
      ((largeFiberRows U f t).filter (fun y => f y = a)).card + t := by
    by_cases ha : t ≤ (U.filter (fun y => f y = a)).card
    · rw [largeFiberRows_fiber_eq U f t a ha]
      omega
    · omega
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => hfiber a)
  rw [Finset.sum_add_distrib, sum_assignment_fiber_cards, sum_assignment_fiber_cards] at hsum
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hsum

end Erdos911
