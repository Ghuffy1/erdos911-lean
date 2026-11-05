import Erdos911.FiniteAveraging
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

namespace Erdos911

theorem incidence_card_sum_comm {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (r : A → B → Prop) [DecidableRel r] :
    (∑ a ∈ S, (T.filter (r a)).card) =
      ∑ b ∈ T, (S.filter (fun a => r a b)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A finite family with bounded incidence at every point has a member
whose size is at most the incidence average, expressed without division. -/
theorem exists_small_incidence_fiber {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (r : A → B → Prop) [DecidableRel r]
    (hS : S.Nonempty) (C : ℕ)
    (hC : ∀ b ∈ T, (S.filter (fun a => r a b)).card ≤ C) :
    ∃ a ∈ S, (T.filter (r a)).card * S.card ≤ T.card * C := by
  have hsum : (∑ a ∈ S, (T.filter (r a)).card) ≤ T.card * C := by
    rw [incidence_card_sum_comm]
    calc
      (∑ b ∈ T, (S.filter (fun a => r a b)).card) ≤ ∑ _b ∈ T, C := Finset.sum_le_sum hC
      _ = T.card * C := by simp
  by_contra h
  push Not at h
  have hstrict : ∀ a ∈ S, T.card * C < (T.filter (r a)).card * S.card := by
    intro a ha
    exact h a ha
  have hsumstrict := Finset.sum_lt_sum_of_nonempty hS hstrict
  have hscaled := Nat.mul_le_mul_right S.card hsum
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul] at hsumstrict
  nlinarith

/-- Real-valued incidence bounds support exponential counting estimates
without rounding the bound to a natural number. -/
theorem exists_small_incidence_fiber_real {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (r : A → B → Prop) [DecidableRel r]
    (hS : S.Nonempty) (C : ℝ)
    (hC : ∀ b ∈ T, ((S.filter (fun a => r a b)).card : ℝ) ≤ C) :
    ∃ a ∈ S, ((T.filter (r a)).card : ℝ) * S.card ≤ T.card * C := by
  have hsum : (∑ a ∈ S, ((T.filter (r a)).card : ℝ)) ≤ T.card * C := by
    have hswap : (∑ a ∈ S, ((T.filter (r a)).card : ℝ)) =
        ∑ b ∈ T, ((S.filter (fun a => r a b)).card : ℝ) := by
      exact_mod_cast incidence_card_sum_comm S T r
    rw [hswap]
    calc
      (∑ b ∈ T, ((S.filter (fun a => r a b)).card : ℝ)) ≤ ∑ _b ∈ T, C :=
        Finset.sum_le_sum hC
      _ = T.card * C := by simp
  by_contra h
  push Not at h
  have hsumstrict := Finset.sum_lt_sum_of_nonempty hS h
  have hscaled := mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg (α := ℝ) S.card)
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul] at hsumstrict
  nlinarith

theorem exists_two_supports_small {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (R P : A → Finset B)
    (hS : S.Nonempty) (hR : ∀ a ∈ S, R a ⊆ T) (hP : ∀ a ∈ S, P a ⊆ T)
    (CR CP : ℝ)
    (hCR : ∀ b ∈ T, ((S.filter (fun a => b ∈ R a)).card : ℝ) ≤ CR)
    (hCP : ∀ b ∈ T, ((S.filter (fun a => b ∈ P a)).card : ℝ) ≤ CP) :
    ∃ a ∈ S, ((R a ∪ P a).card : ℝ) * S.card ≤ T.card * (CR + CP) := by
  classical
  have hC : ∀ b ∈ T, ((S.filter (fun a => b ∈ R a ∪ P a)).card : ℝ) ≤ CR + CP := by
    intro b hb
    have hfilter : S.filter (fun a => b ∈ R a ∪ P a) =
        S.filter (fun a => b ∈ R a) ∪ S.filter (fun a => b ∈ P a) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_union, and_or_left]
    have hcard : ((S.filter (fun a => b ∈ R a ∪ P a)).card : ℝ) ≤
        (S.filter (fun a => b ∈ R a)).card + (S.filter (fun a => b ∈ P a)).card := by
      rw [hfilter]
      exact_mod_cast Finset.card_union_le (S.filter (fun a => b ∈ R a)) (S.filter (fun a => b ∈ P a))
    linarith [hCR b hb, hCP b hb]
  obtain ⟨a, ha, hsmall⟩ := exists_small_incidence_fiber_real S T (fun a b => b ∈ R a ∪ P a) hS (CR + CP) hC
  have hfilter : T.filter (fun b => b ∈ R a ∪ P a) = R a ∪ P a := by
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(Finset.union_subset (hR a ha) (hP a ha)) h, h⟩⟩
  rw [hfilter] at hsmall
  exact ⟨a, ha, hsmall⟩

end Erdos911
