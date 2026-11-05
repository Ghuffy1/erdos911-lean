import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

namespace Erdos911

/-- A positive-size sample can retain a strict lower bound on the average.
The proof removes entries below the bound until either the requested size is
reached or every remaining entry exceeds the bound. -/
theorem exists_subset_card_sum_gt {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (r : ℝ) (q : ℕ) (hq : 0 < q) (hlen : q ≤ S.card)
    (hsum : r * S.card < ∑ x ∈ S, f x) :
    ∃ T ⊆ S, T.card = q ∧ r * q < ∑ x ∈ T, f x := by
  classical
  revert hlen hsum
  refine Finset.strongInductionOn S ?_
  intro S ih hlen hsum
  by_cases heq : S.card = q
  · exact ⟨S, Finset.Subset.refl _, heq, by simpa [heq] using hsum⟩
  by_cases hex : ∃ x ∈ S, f x ≤ r
  · obtain ⟨x, hx, hxr⟩ := hex
    have hcard := Finset.card_erase_add_one hx
    have hlen' : q ≤ (S.erase x).card := by omega
    have hcast : (S.card : ℝ) = (S.erase x).card + 1 := by
      exact_mod_cast hcard.symm
    have hsum' : r * (S.erase x).card < ∑ y ∈ S.erase x, f y := by
      have hsplit := Finset.sum_erase_add S f hx
      rw [hcast] at hsum
      nlinarith
    obtain ⟨T, hT, hsize, hsumT⟩ :=
      ih (S.erase x) (Finset.erase_ssubset hx) hlen' hsum'
    exact ⟨T, hT.trans (Finset.erase_subset _ _), hsize, hsumT⟩
  · obtain ⟨T, hT, hsize⟩ := Finset.exists_subset_card_eq hlen
    refine ⟨T, hT, hsize, ?_⟩
    have hnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
    have hterm : ∀ x ∈ T, r < f x := by
      intro x hx
      by_contra h
      exact hex ⟨x, hT hx, le_of_not_gt h⟩
    have hstrict := Finset.sum_lt_sum_of_nonempty hnonempty hterm
    simpa [hsize, mul_comm] using hstrict

end Erdos911
