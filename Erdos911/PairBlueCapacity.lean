import Erdos911.ConcretePairMarking

namespace Erdos911

/-- A retained blue incidence pattern whose nonempty rows avoid the bad
host rows has at most half the target's full right-degree capacity. -/
theorem pair_blue_incidence_capacity {A B L R : Type*}
    [DecidableEq A] [Fintype B] [DecidableEq L] [Fintype R]
    (T : B → Finset A) (N : R → Finset L) (l : A → L) (hl : Function.Injective l)
    (r : B → R) (d : ℕ) (ω : Sym2 L → Bool)
    (hblue : ∀ y x, x ∈ T y → l x ∈ pairBlueRow (N (r y)) ω)
    (hgood : ∀ y, (T y).Nonempty → r y ∉ pairBadRows N d ω) :
    2 * (∑ y, (T y).card) ≤ d * Fintype.card B := by
  classical
  have hrow (y : B) : 2 * (T y).card ≤ d := by
    by_cases hne : (T y).Nonempty
    · have hbad : ¬ d ≤ 2 * (pairBlueRow (N (r y)) ω).card := by
        intro h
        exact hgood y hne (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hcard : (T y).card ≤ (pairBlueRow (N (r y)) ω).card := by
        calc
          _ = ((T y).image l).card := (Finset.card_image_of_injective _ hl).symm
          _ ≤ _ := Finset.card_le_card (by
            intro x hx
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
            exact hblue y a ha)
      omega
    · have hz : T y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [hz, Finset.card_empty, mul_zero]
      exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset B)) => hrow y)
  rw [← Finset.mul_sum] at hsum
  simpa [mul_comm] using hsum

/-- Removing target rows whose injective images are bad costs at most
d edges per bad host row. -/
theorem pair_bad_row_edge_cost {A B R : Type*} [Fintype B] [DecidableEq R]
    (S : B → Finset A) (d : ℕ) (hrow : ∀ y, (S y).card = d)
    (r : B → R) (hr : Function.Injective r) (bad : Finset R) :
    (∑ y ∈ Finset.univ.filter (fun y => r y ∈ bad), (S y).card) ≤ d * bad.card := by
  classical
  let C := (Finset.univ : Finset B).filter (fun y => r y ∈ bad)
  have hcard : C.card ≤ bad.card := by
    calc
      C.card = (C.image r).card := (Finset.card_image_of_injective _ hr).symm
      _ ≤ bad.card := Finset.card_le_card (by
        intro y hy
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hb).2)
  have hmul := Nat.mul_le_mul_left d hcard
  simpa [C, hrow, mul_comm] using hmul

/-- The conditional row tail is small enough for the original host edge
budget, without any dependence on the left degree scale. -/
theorem pair_bad_row_budget (d : ℕ) (hd : 65536 ≤ d) (b : ℕ) (e Λ : ℝ)
    (hΛ : Λ ≤ (d : ℝ) ^ 2) (he : 0 ≤ e) (hb : (b : ℝ) ≤ 2 * Λ * e) :
    (2 / (d : ℝ) ^ 8) * b ≤ e / (8 * d) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
  have hd5 : (32 : ℝ) ≤ (d : ℝ) ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hdr 5
    norm_num at h
    exact h
  have h₁ := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 / (d : ℝ) ^ 8 by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hΛ (show 0 ≤ 4 * e / (d : ℝ) ^ 8 by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hd5 he
  have hden : (d : ℝ) ^ 8 = (d : ℝ) ^ 5 * (d : ℝ) ^ 3 := by rw [← pow_add]
  have hclaim : (4 * (d : ℝ) ^ 2 * e) / (d : ℝ) ^ 8 ≤ e / (8 * d) := by
    apply (div_le_div_iff₀ (pow_pos hdp 8) (by positivity : 0 < 8 * (d : ℝ))).mpr
    have hmul := mul_le_mul_of_nonneg_right h₃ (pow_nonneg hdp.le 3)
    nlinarith only [hmul, hden]
  calc
    _ ≤ (2 / (d : ℝ) ^ 8) * (2 * Λ * e) := h₁
    _ = (4 * Λ * e) / (d : ℝ) ^ 8 := by ring
    _ ≤ (4 * (d : ℝ) ^ 2 * e) / (d : ℝ) ^ 8 := by convert h₂ using 1 <;> ring
    _ ≤ _ := hclaim

end Erdos911
