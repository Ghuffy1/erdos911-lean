import Erdos911.Statement
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter SimpleGraph

namespace Erdos911

/-- A function with divergent ratio gives every fixed integer multiplier. -/
theorem fixedMultipliers_of_exact (h : ExactStatement) : FixedMultiplierStatement := by
  rcases h with ⟨f, hlim, C₀, hbound⟩
  intro k
  obtain ⟨t, ht⟩ := tendsto_atTop_atTop.mp hlim (k : ℝ)
  refine ⟨max C₀ (max t 1), ?_⟩
  intro C hC n G hn hedges
  have hC₀ : C₀ ≤ C := (le_max_left _ _).trans hC
  have htC : t ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans hC)
  have hOne : (1 : ℝ) ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hC)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hOne
  have hmult : (k : ℝ) * C ≤ f C := (le_div_iff₀ hCpos).mp (ht C htC)
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hmult (Nat.cast_nonneg _))
    (hbound C hC₀ n G hn hedges)

/-- A diagonal choice converts all fixed multipliers into the exact function
quantifier. The diagonal thresholds are chosen from the supplied statement. -/
theorem exact_of_fixedMultipliers (h : FixedMultiplierStatement) : ExactStatement := by
  classical
  choose c hc using h
  let A : ℕ → ℝ := fun k => max (k : ℝ) (c k)
  let g : ℝ → ℕ := fun C => Nat.findGreatest (fun k => A k ≤ C) ⌊C⌋₊
  let f : ℝ → ℝ := fun C => C * (g C : ℝ)
  refine ⟨f, ?_, max (A 0) 1, ?_⟩
  · apply tendsto_atTop_atTop.mpr
    intro b
    obtain ⟨k, hk⟩ := exists_nat_gt b
    refine ⟨max (A k) 1, ?_⟩
    intro C hC
    have hA : A k ≤ C := (le_max_left _ _).trans hC
    have hkC : (k : ℝ) ≤ C := (le_max_left _ _).trans hA
    have hkg : k ≤ g C := Nat.le_findGreatest (Nat.le_floor hkC) hA
    have hOne : (1 : ℝ) ≤ C := (le_max_right _ _).trans hC
    have hCne : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hOne)
    have hb : b ≤ (g C : ℝ) := (le_of_lt hk).trans (by exact_mod_cast hkg)
    simpa [f, hCne] using hb
  · intro C hC n G hn hedges
    have hA₀ : A 0 ≤ C := (le_max_left _ _).trans hC
    have hg : A (g C) ≤ C := by
      exact Nat.findGreatest_spec (P := fun k => A k ≤ C) (Nat.zero_le _) hA₀
    have hthreshold : c (g C) ≤ C := (le_max_right _ _).trans hg
    have hresult := hc (g C) C hthreshold n G hn hedges
    simpa [f, mul_comm C (g C : ℝ)] using hresult

/-- The exact target and the uniform fixed-multiplier statement are equivalent.
Neither side is asserted here without a proof of the other. -/
theorem exact_iff_fixedMultipliers : ExactStatement ↔ FixedMultiplierStatement :=
  ⟨fixedMultipliers_of_exact, exact_of_fixedMultipliers⟩

end Erdos911
