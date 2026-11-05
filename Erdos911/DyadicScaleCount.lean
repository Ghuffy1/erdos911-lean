import Erdos911.DictionaryParameters
import Mathlib.Order.Interval.Finset.Nat

namespace Erdos911

/-- A multiplicative range bound on powers of two gives a uniform,
deliberately coarse bound on the number of admissible exponents. -/
theorem dyadic_scale_card_bound (S : Finset ℕ) (B : ℕ)
    (hpair : ∀ j ∈ S, ∀ k ∈ S, 2 ^ j < B * 2 ^ k) : S.card ≤ B := by
  classical
  by_cases hS : S.Nonempty
  · let k := S.min' hS
    have hk : k ∈ S := Finset.min'_mem S hS
    have hsub : S ⊆ Finset.Ico k (k + B) := by
      intro j hj
      have hlo : k ≤ j := Finset.min'_le S j hj
      have hp := (hpair j hj k hk).trans_le (Nat.mul_le_mul_right (2 ^ k) (Nat.le_of_lt B.lt_two_pow_self))
      rw [← pow_add] at hp
      have hhi : j < B + k := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hp
      exact Finset.mem_Ico.mpr ⟨hlo, by omega⟩
    have h := Finset.card_le_card hsub
    simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using h
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.zero_le]

end Erdos911
