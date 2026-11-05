import Erdos911.ForestEntropy
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos911

/-- A finite entropy bound from a reference distribution whose mass is at
most one. The multiplicities need not be equal. -/
theorem multiplicityEntropy_le_cost {I : Type*} [Fintype I]
    (t : I → ℕ) (cost : I → ℝ)
    (hr : 0 < ∑ i, (t i : ℝ)) (hpartition : ∑ i, Real.exp (-cost i) ≤ 1) :
    multiplicityEntropy t ≤ ∑ i, (t i : ℝ) * cost i := by
  let r : ℝ := ∑ i, (t i : ℝ)
  have hrpos : 0 < r := hr
  have hpoint (i : I) : (t i : ℝ) * Real.log r - (t i : ℝ) * cost i -
      (t i : ℝ) * Real.log (t i : ℝ) ≤ r * Real.exp (-cost i) - t i := by
    by_cases hzero : t i = 0
    · simp only [hzero, Nat.cast_zero, zero_mul, sub_zero]
      positivity
    have hi : (0 : ℝ) < t i := by exact_mod_cast Nat.pos_of_ne_zero hzero
    have hratio : 0 < r * Real.exp (-cost i) / t i := by positivity
    have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) hi.le
    rw [Real.log_div (by positivity) hi.ne',
      Real.log_mul hrpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h
    have hcancel : (t i : ℝ) * (r * Real.exp (-cost i) / t i) =
        r * Real.exp (-cost i) := by field_simp
    nlinarith only [h, hcancel]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hpoint i)
  have hleft : (∑ i, ((t i : ℝ) * Real.log r - (t i : ℝ) * cost i -
      (t i : ℝ) * Real.log (t i : ℝ))) = multiplicityEntropy t - ∑ i, (t i : ℝ) * cost i := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, multiplicityEntropy, r]
    ring
  have hright : (∑ i, (r * Real.exp (-cost i) - t i)) =
      r * (∑ i, Real.exp (-cost i)) - r := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hleft, hright] at hsum
  have hmass := mul_le_mul_of_nonneg_left hpartition hrpos.le
  linarith

theorem positive_geometric_sum_le_one (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) :
    (∑ a ∈ S, (1 / 2 : ℝ) ^ a) ≤ 1 := by
  let N := S.sup id + 1
  have hsub : S ⊆ (Finset.range N).erase 0 := by
    intro a ha
    refine Finset.mem_erase.mpr ⟨Nat.ne_of_gt (hS a ha), ?_⟩
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  have hbound : (∑ a ∈ S, (1 / 2 : ℝ) ^ a) ≤
      ∑ a ∈ (Finset.range N).erase 0, (1 / 2 : ℝ) ^ a :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr (by dsimp [N]; omega)
  have hsplit := Finset.sum_erase_add (Finset.range N) (fun a => (1 / 2 : ℝ) ^ a) hzero
  have hfull := sum_geometric_two_le N
  norm_num only [pow_zero] at hsplit
  linarith

theorem positive_pair_geometric_sum_le_one (P : Finset (ℕ × ℕ))
    (hP : ∀ p ∈ P, 0 < p.1 ∧ 0 < p.2) :
    (∑ p ∈ P, (1 / 2 : ℝ) ^ (p.1 + p.2)) ≤ 1 := by
  classical
  let A := P.image Prod.fst
  let B := P.image Prod.snd
  have hA : (∑ a ∈ A, (1 / 2 : ℝ) ^ a) ≤ 1 := by
    apply positive_geometric_sum_le_one
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (hP p hp).1
  have hB : (∑ b ∈ B, (1 / 2 : ℝ) ^ b) ≤ 1 := by
    apply positive_geometric_sum_le_one
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact (hP p hp).2
  have hsub : P ⊆ A ×ˢ B := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  calc
    (∑ p ∈ P, (1 / 2 : ℝ) ^ (p.1 + p.2)) ≤
        ∑ p ∈ A ×ˢ B, (1 / 2 : ℝ) ^ (p.1 + p.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ a ∈ A, ∑ b ∈ B, (1 / 2 : ℝ) ^ a * (1 / 2 : ℝ) ^ b := by
      rw [Finset.sum_product]
      simp only [pow_add]
    _ = (∑ a ∈ A, (1 / 2 : ℝ) ^ a) * (∑ b ∈ B, (1 / 2 : ℝ) ^ b) :=
      (Finset.sum_mul_sum A B _ _).symm
    _ ≤ 1 := by
      have h := mul_le_mul hA hB (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using h

end Erdos911
