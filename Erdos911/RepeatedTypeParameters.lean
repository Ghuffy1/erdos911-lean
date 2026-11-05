import Erdos911.RepeatedTypeBounds
import Erdos911.ComponentClasses

open Filter Asymptotics

namespace Erdos911

theorem component_entropy_error_tends_to_zero (C : ℝ) :
    Tendsto (fun x : ℝ => (Real.log (Real.log x) + C) / Real.log x) atTop (nhds 0) := by
  have hlog : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x => Real.log x) :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have h := hlog.tendsto_div_nhds_zero.add (hinv.const_mul C)
  have heq : (fun x : ℝ => (Real.log (Real.log x) + C) / Real.log x) =
      (fun x => Real.log (Real.log x) / Real.log x + C * (Real.log x)⁻¹) := by
    funext x
    ring
  rw [heq]
  simpa only [mul_zero, add_zero] using h

theorem eventually_component_entropy_lower (C : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      (1 - 1 / 32768 : ℝ) * Real.log d ≤ Real.log d - Real.log (Real.log d) - C := by
  have he := (component_entropy_error_tends_to_zero C).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 32768 by norm_num))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hl.and he)
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd
  obtain ⟨hlog, herr⟩ := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast hd))
  have hlogpos : 0 < Real.log d := by linarith
  have h := (div_lt_iff₀ hlogpos).mp herr
  linarith

theorem polynomial_counterexample_class_lower (A B : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) →
      (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      (SimpleGraph.sizeRamsey G G : ℝ) ≤ (d : ℝ) ^ A * G.edgeSet.ncard →
      ∃ t : ComponentType G,
        Real.exp ((1 - 1 / 32768 : ℝ) * componentSize G t * Real.log d) <
          ((componentClass G (componentOrder G t) (componentSize G t)).card : ℝ) := by
  obtain ⟨C, d₁, hd₁⟩ := polynomial_counterexample_large_class A B
  obtain ⟨d₂, hd₂⟩ := eventually_component_entropy_lower C
  refine ⟨max d₁ d₂, ?_⟩
  intro d hd n G hn hmin hmax hcheap
  obtain ⟨t, ht⟩ := hd₁ d ((le_max_left _ _).trans hd) n G hn hmin hmax hcheap
  have h := mul_le_mul_of_nonneg_left (hd₂ d ((le_max_right _ _).trans hd))
    (Nat.cast_nonneg (α := ℝ) (componentSize G t))
  refine ⟨t, lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) ht⟩
  nlinarith only [h]

theorem repeated_type_support_log_gap (x Λ L X : ℝ) (a : ℕ)
    (hlog : 32768 ≤ Real.log x) (hΛ : 0 < Λ) (hΛx : Λ ≤ x)
    (ha : 65536 ≤ a) (hL : (1 - 1 / 32768 : ℝ) * Real.log x ≤ L)
    (hX : X ≤ (1 - 1 / 16384 : ℝ) * a * Real.log x) :
    X ≤ L * a + Real.log (1 / (16 * Λ)) := by
  have hlogΛ : Real.log Λ ≤ Real.log x := Real.log_le_log hΛ hΛx
  have hlog16 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)
  norm_num at hlog16
  have hlogprod : Real.log (16 * Λ) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hΛ.ne']
    linarith
  have haR : (65536 : ℝ) ≤ a := by exact_mod_cast ha
  have hmargin := mul_le_mul_of_nonneg_right haR (show 0 ≤ Real.log x by linarith)
  have hclass := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg (α := ℝ) a)
  rw [Real.log_div (by norm_num) (mul_pos (by norm_num) hΛ).ne', Real.log_one, zero_sub]
  nlinarith only [hmargin, hclass, hX, hlogprod]

theorem repeated_threshold_bounds (a : ℕ) (ha : 65536 ≤ a) :
    2 * (a / 1024) ≤ a ∧ (a : ℝ) / 2048 ≤ (a / 1024 : ℕ) := by
  have h : a ≤ 2048 * (a / 1024) := by omega
  refine ⟨by omega, ?_⟩
  have hR : (a : ℝ) ≤ 2048 * (a / 1024 : ℕ) := by exact_mod_cast h
  linarith

end Erdos911
