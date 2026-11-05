import Erdos911.BlockParameterBounds

open Filter

namespace Erdos911

noncomputable def linearBlockCostConstant (A : ℕ) (C M : ℝ) : ℝ :=
  1048576 * ((A : ℝ) + 1) * C * M

theorem linear_host_block_cost (A : ℕ) (C M x e m : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hx : 0 < x) (hlog : 1 ≤ Real.log x) (he : 0 ≤ e)
    (hm : m ≤ (M * x) * e) :
    32 * baselineBlockRate A x * (C * Real.log x) * m / (baselineBlockSize x : ℝ) ≤
      linearBlockCostConstant A C M * e / (Real.log x) ^ 2 := by
  have hLpos : 0 < Real.log x := by linarith
  have hq : (Real.log x) ^ 4 ≤ (baselineBlockSize x : ℝ) := Nat.le_ceil _
  have hqpos : (0 : ℝ) < baselineBlockSize x := (pow_pos hLpos 4).trans_le hq
  have hp : 0 ≤ baselineBlockRate A x := by unfold baselineBlockRate; positivity
  have hfrac : (Real.log x) ^ 2 / (baselineBlockSize x : ℝ) ≤ 1 / (Real.log x) ^ 2 := by
    apply (div_le_div_iff₀ hqpos (by positivity)).mpr
    nlinarith only [hq]
  calc
    _ ≤ 32 * baselineBlockRate A x * (C * Real.log x) * ((M * x) * e) /
        (baselineBlockSize x : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) hqpos.le
    _ = (linearBlockCostConstant A C M * e) * ((Real.log x) ^ 2 / (baselineBlockSize x : ℝ)) := by
      unfold baselineBlockRate linearBlockCostConstant
      field_simp
      ring
    _ ≤ (linearBlockCostConstant A C M * e) * (1 / (Real.log x) ^ 2) :=
      mul_le_mul_of_nonneg_left hfrac (by unfold linearBlockCostConstant; positivity)
    _ = _ := by ring

theorem entropy_block_capacity (A : ℕ) (C M x e m : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hx : 0 < x) (hlog : 1 ≤ Real.log x) (he : 0 ≤ e)
    (hm : m ≤ (M * x) * e) (hscale : 16 * linearBlockCostConstant A C M ≤ Real.log x) :
    32 * baselineBlockRate A x * (C * Real.log x) * m / (baselineBlockSize x : ℝ) ≤ e / (16 * Real.log x) := by
  apply (linear_host_block_cost A C M x e m hC hM hx hlog he hm).trans
  have hLpos : 0 < Real.log x := by linarith
  have h := mul_le_mul_of_nonneg_right hscale he
  calc
    linearBlockCostConstant A C M * e / (Real.log x) ^ 2 =
        (16 * linearBlockCostConstant A C M * e) / (16 * (Real.log x) ^ 2) := by ring
    _ ≤ (Real.log x * e) / (16 * (Real.log x) ^ 2) :=
      div_le_div_of_nonneg_right h (by positivity)
    _ = e / (16 * Real.log x) := by field_simp

theorem entropy_total_capacity (A : ℕ) (C M x e m : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hx : 0 < x) (hlog : 1 ≤ Real.log x) (he : 0 ≤ e)
    (hm : m ≤ (M * x) * e) (hscale : 16 * linearBlockCostConstant A C M ≤ Real.log x) :
    e / (4 * Real.log x) + (2 * baselineBlockRate A x) *
      (2 * (C * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x) +
       2 * (C * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x)) ≤ e / Real.log x := by
  have hLpos : 0 < Real.log x := by linarith
  have hq : (Real.log x) ^ 4 ≤ (baselineBlockSize x : ℝ) := Nat.le_ceil _
  have hqpos : (0 : ℝ) < baselineBlockSize x := (pow_pos hLpos 4).trans_le hq
  have hcost := entropy_block_capacity A C M x e m hC hM hx hlog he hm hscale
  have heq : (2 * baselineBlockRate A x) *
      (2 * (C * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x) +
       2 * (C * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x)) =
      32 * baselineBlockRate A x * (C * Real.log x) * m / (baselineBlockSize x : ℝ) := by
    field_simp
    ring
  rw [heq]
  have hnonneg : 0 ≤ e / Real.log x := div_nonneg he hLpos.le
  have hfour : e / (4 * Real.log x) = (e / Real.log x) / 4 := by ring
  have hsixteen : e / (16 * Real.log x) = (e / Real.log x) / 16 := by ring
  have hcost' := hcost.trans_eq hsixteen
  rw [hfour]
  linarith

theorem eventually_entropy_block_capacity (A : ℕ) (C M : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 16 * linearBlockCostConstant A C M ≤ Real.log d := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (16 * linearBlockCostConstant A C M)))
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd
  exact hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast hd))

end Erdos911
