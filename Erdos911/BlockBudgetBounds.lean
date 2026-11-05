import Erdos911.BlockParameterBounds

open Filter

namespace Erdos911

noncomputable def baselineHostMultiplier (x : ℝ) : ℝ :=
  x / (16384 * Real.log (Real.log x))

noncomputable def baselineBlockBudgetError (A : ℕ) (B x : ℝ) : ℝ :=
  64 * ((A : ℝ) + 1) * B / (Real.log x) ^ 2

theorem baselineBlockBudgetError_tends_to_zero (A : ℕ) (B : ℝ) :
    Tendsto (baselineBlockBudgetError A B) atTop (nhds 0) := by
  have h : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hs := (h.pow 2).const_mul (64 * ((A : ℝ) + 1) * B)
  change Tendsto (fun x : ℝ => 64 * ((A : ℝ) + 1) * B / (Real.log x) ^ 2) atTop (nhds 0)
  simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, div_eq_mul_inv, inv_pow] using hs

theorem baseline_residual_cost (x e m : ℝ) (hx : 0 < x)
    (hloglog : 1 ≤ Real.log (Real.log x))
    (hm : m ≤ baselineHostMultiplier x * e) :
    2 * baselineResidualRate x * m ≤ e / 32 := by
  have hloglogpos : 0 < Real.log (Real.log x) := by linarith
  have hp : 0 ≤ baselineResidualRate x := by unfold baselineResidualRate; positivity
  calc
    2 * baselineResidualRate x * m ≤ 2 * baselineResidualRate x * (baselineHostMultiplier x * e) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = e / 32 := by
      unfold baselineResidualRate baselineHostMultiplier
      field_simp
      ring

theorem baseline_block_cost (A : ℕ) (B x e m : ℝ) (hB : 0 ≤ B) (hx : 0 < x)
    (hlog : 1 ≤ Real.log x) (hloglog : 1 ≤ Real.log (Real.log x)) (he : 0 ≤ e)
    (hm : m ≤ baselineHostMultiplier x * e) :
    32 * baselineBlockRate A x * (B * Real.log x) * m / (baselineBlockSize x : ℝ) ≤
      baselineBlockBudgetError A B x * e := by
  have hlogpos : 0 < Real.log x := by linarith
  have hloglogpos : 0 < Real.log (Real.log x) := by linarith
  have hq : (Real.log x) ^ 4 ≤ (baselineBlockSize x : ℝ) := Nat.le_ceil _
  have hqpos : (0 : ℝ) < baselineBlockSize x := (pow_pos hlogpos _).trans_le hq
  have hp : 0 ≤ baselineBlockRate A x := by unfold baselineBlockRate; positivity
  have hscaled := mul_le_mul_of_nonneg_right hloglog (Nat.cast_nonneg (α := ℝ) (baselineBlockSize x))
  have hfrac : (Real.log x) ^ 2 /
      (Real.log (Real.log x) * (baselineBlockSize x : ℝ)) ≤ 1 / (Real.log x) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [hq, hscaled]
  calc
    32 * baselineBlockRate A x * (B * Real.log x) * m / (baselineBlockSize x : ℝ) ≤
        32 * baselineBlockRate A x * (B * Real.log x) *
          (baselineHostMultiplier x * e) / (baselineBlockSize x : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) hqpos.le
    _ = (64 * ((A : ℝ) + 1) * B * e) *
        ((Real.log x) ^ 2 / (Real.log (Real.log x) * (baselineBlockSize x : ℝ))) := by
      unfold baselineBlockRate baselineHostMultiplier
      field_simp
      ring
    _ ≤ (64 * ((A : ℝ) + 1) * B * e) * (1 / (Real.log x) ^ 2) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = baselineBlockBudgetError A B x * e := by unfold baselineBlockBudgetError; ring

theorem baseline_two_scale_budget (A : ℕ) (B x e m L : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hlog : 1 ≤ Real.log x)
    (hloglog : 1 ≤ Real.log (Real.log x)) (he : 0 < e)
    (hm : m ≤ baselineHostMultiplier x * e) (hL : L ≤ e / 4)
    (herror : baselineBlockBudgetError A B x ≤ 1 / 16) :
    L + (2 * baselineBlockRate A x) *
      (2 * (B * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x) +
       2 * (B * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x)) +
      2 * baselineResidualRate x * m < e := by
  have hq : (Real.log x) ^ 4 ≤ (baselineBlockSize x : ℝ) := Nat.le_ceil _
  have hqpos : (0 : ℝ) < baselineBlockSize x := (pow_pos (by linarith : 0 < Real.log x) _).trans_le hq
  have hblock := baseline_block_cost A B x e m hB hx hlog hloglog he.le hm
  have hresidual := baseline_residual_cost x e m hx hloglog hm
  have hblock' : 32 * baselineBlockRate A x * (B * Real.log x) * m /
      (baselineBlockSize x : ℝ) ≤ e / 16 := by
    have h := mul_le_mul_of_nonneg_right herror he.le
    nlinarith only [hblock, h]
  have heq : (2 * baselineBlockRate A x) *
      (2 * (B * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x) +
       2 * (B * Real.log x) * m / ((1 / 4 : ℝ) * baselineBlockSize x)) =
      32 * baselineBlockRate A x * (B * Real.log x) * m / (baselineBlockSize x : ℝ) := by
    field_simp
    ring
  rw [heq]
  linarith

theorem eventually_baseline_block_budget (A : ℕ) (B : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, baselineBlockBudgetError A B d ≤ 1 / 16 := by
  have h := (baselineBlockBudgetError_tends_to_zero A B).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd
  exact (hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast hd))).le

end Erdos911
