import Erdos911.EntropyHostParameters
import Erdos911.RepeatedTypeParameters

open Filter

namespace Erdos911

noncomputable def entropyTypeLogConstant (B : ℕ) (M : ℝ) : ℝ := 4096 * ((B : ℝ) + 1) * M

theorem entropyHostDensityCutoff_upper (d : ℕ) (hd : 1 ≤ d) (hlog : 1 ≤ Real.log d) :
    (entropyHostDensityCutoff d : ℝ) ≤ 2 * (d : ℝ) ^ 2 * (Real.log d) ^ 3 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ hdR
  have hL3 : (1 : ℝ) ≤ (Real.log d) ^ 3 := one_le_pow₀ hlog
  have hscaled := mul_le_mul_of_nonneg_left hL3 (show 0 ≤ (d : ℝ) ^ 2 by positivity)
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ (d : ℝ) ^ 2 * (Real.log d) ^ 3 by positivity)).le
  change (entropyHostDensityCutoff d : ℝ) ≤ _ at hceil
  nlinarith only [hd2, hscaled, hceil]

theorem entropy_available_ratio_upper (d k a : ℕ) (hd : 1 ≤ d) (ha : 0 < a)
    (hlog : 1 ≤ Real.log d) (haverage : d * k ≤ 2 * a) :
    ((entropyHostDensityCutoff d * k : ℕ) : ℝ) / a ≤ 4 * d * (Real.log d) ^ 3 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hscaled := mul_le_mul_of_nonneg_right (entropyHostDensityCutoff_upper d hd hlog)
    (Nat.cast_nonneg (α := ℝ) k)
  have havg : (d : ℝ) * k ≤ 2 * a := by exact_mod_cast haverage
  have havgScaled := mul_le_mul_of_nonneg_left havg
    (show 0 ≤ 2 * (d : ℝ) * (Real.log d) ^ 3 by positivity)
  apply (div_le_iff₀ haR).mpr
  rw [Nat.cast_mul]
  nlinarith only [hscaled, havgScaled]

theorem entropy_available_ratio_lower (B d k a R : ℕ) (M : ℝ) (ha : 0 < a) (hR : 0 < R)
    (hd : 1 ≤ d) (hM : 1 ≤ M) (hlog : 1 ≤ Real.log d)
    (hdensity : (a : ℝ) ≤ entropyTargetDensity B M d * k) :
    ((d : ℝ) * (Real.log d) ^ 2 / entropyTypeLogConstant B M) / R ≤
      ((entropyHostDensityCutoff d * k : ℕ) : ℝ) / ((a : ℝ) * R) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hK : 0 < entropyTypeLogConstant B M := by unfold entropyTypeLogConstant; positivity
  have hceil : (d : ℝ) ^ 2 * (Real.log d) ^ 3 ≤ (entropyHostDensityCutoff d : ℝ) := Nat.le_ceil _
  have hdenseScaled := mul_le_mul_of_nonneg_left hdensity
    (show 0 ≤ (d : ℝ) * (Real.log d) ^ 2 by positivity)
  have hceilScaled := mul_le_mul_of_nonneg_right hceil
    (show 0 ≤ entropyTypeLogConstant B M * k by positivity)
  have hratio : (d : ℝ) * (Real.log d) ^ 2 / entropyTypeLogConstant B M ≤
      ((entropyHostDensityCutoff d * k : ℕ) : ℝ) / a := by
    apply (div_le_div_iff₀ hK haR).mpr
    rw [Nat.cast_mul]
    unfold entropyTargetDensity at hdenseScaled
    unfold entropyTypeLogConstant at hceilScaled ⊢
    nlinarith only [hdenseScaled, hceilScaled]
  simpa only [div_div] using div_le_div_of_nonneg_right hratio hRreal.le

theorem entropy_available_log_bounds (B d k a : ℕ) (M : ℝ) (hd : 1 ≤ d) (ha : 0 < a)
    (hM : 1 ≤ M) (hlog : 1 ≤ Real.log d) (hloglog : 1 ≤ Real.log (Real.log d))
    (haverage : d * k ≤ 2 * a) (hdensity : (a : ℝ) ≤ entropyTargetDensity B M d * k) :
    Real.log (((entropyHostDensityCutoff d * k : ℕ) : ℝ) / a) ≤
      Real.log d + 3 * Real.log (Real.log d) + Real.log 4 ∧
    Real.log d - 10 * Real.log (Real.log d) - Real.log (entropyTypeLogConstant B M) ≤
      Real.log (((entropyHostDensityCutoff d * k : ℕ) : ℝ) /
        ((a : ℝ) * (baselineBlockSize d * baselineBlockSize d : ℕ))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hLpos : 0 < Real.log d := by linarith
  have hKpos : 0 < entropyTypeLogConstant B M := by unfold entropyTypeLogConstant; positivity
  have hqpos : (0 : ℝ) < baselineBlockSize d :=
    (pow_pos hLpos 4).trans_le (Nat.le_ceil ((Real.log d) ^ 4))
  have hqnat : 0 < baselineBlockSize d := by exact_mod_cast hqpos
  have hRnat := Nat.mul_pos hqnat hqnat
  have hRpos : (0 : ℝ) < (baselineBlockSize d * baselineBlockSize d : ℕ) := by exact_mod_cast hRnat
  have hsmall := entropy_available_ratio_lower B d k a 1 M ha (by omega) hd hM hlog hdensity
  have hMpos : 0 < ((entropyHostDensityCutoff d * k : ℕ) : ℝ) / a := by
    have hsmall' : (d : ℝ) * (Real.log d) ^ 2 / entropyTypeLogConstant B M ≤
        ((entropyHostDensityCutoff d * k : ℕ) : ℝ) / a := by
      simpa only [Nat.cast_one, div_one, mul_one] using hsmall
    exact (div_pos (mul_pos hdpos (pow_pos hLpos _)) hKpos).trans_le hsmall'
  constructor
  · have h := Real.log_le_log hMpos (entropy_available_ratio_upper d k a hd ha hlog haverage)
    have heq : Real.log (4 * (d : ℝ) * (Real.log d) ^ 3) =
        Real.log d + 3 * Real.log (Real.log d) + Real.log 4 := by
      rw [Real.log_mul (mul_pos (by norm_num) hdpos).ne' (pow_pos hLpos _).ne',
        Real.log_mul (by norm_num) hdpos.ne', Real.log_pow]
      norm_num
      ring
    exact h.trans_eq heq
  · have h := Real.log_le_log
      (div_pos (div_pos (mul_pos hdpos (pow_pos hLpos 2)) hKpos) hRpos)
      (entropy_available_ratio_lower B d k a (baselineBlockSize d * baselineBlockSize d) M
        ha hRnat hd hM hlog hdensity)
    rw [Real.log_div (div_pos (mul_pos hdpos (pow_pos hLpos 2)) hKpos).ne' hRpos.ne',
      Real.log_div (mul_pos hdpos (pow_pos hLpos 2)).ne' hKpos.ne',
      Real.log_mul hdpos.ne' (pow_pos hLpos 2).ne', Real.log_pow] at h
    have hlogq : Real.log (baselineBlockSize d) ≤ 6 * Real.log (Real.log d) :=
      (Real.log_le_log hqpos (by linarith : (baselineBlockSize d : ℝ) ≤
        (baselineBlockSize d : ℝ) + 1)).trans (baselineBlockSize_log_bound d hlog hloglog)
    have hlogR : Real.log ((baselineBlockSize d * baselineBlockSize d : ℕ) : ℝ) ≤
        12 * Real.log (Real.log d) := by
      rw [Nat.cast_mul, Real.log_mul hqpos.ne' hqpos.ne']
      linarith
    norm_num at h
    push_cast at hlogR ⊢
    linarith

noncomputable def entropyTypeLogError (B : ℕ) (M x : ℝ) : ℝ :=
  12 * (Real.log (Real.log x) + Real.log (entropyTypeLogConstant B M) + Real.log 4) / Real.log x

theorem entropyTypeLogError_tends_to_zero (B : ℕ) (M : ℝ) :
    Tendsto (entropyTypeLogError B M) atTop (nhds 0) := by
  have h := (component_entropy_error_tends_to_zero
    (Real.log (entropyTypeLogConstant B M) + Real.log 4)).const_mul 12
  change Tendsto (fun x : ℝ => 12 *
    (Real.log (Real.log x) + Real.log (entropyTypeLogConstant B M) + Real.log 4) / Real.log x)
    atTop (nhds 0)
  simpa only [mul_zero, mul_div_assoc, add_assoc] using h

theorem eventually_entropy_type_log_bounds (B : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k a : ℕ, 0 < a → d * k ≤ 2 * a →
      (a : ℝ) ≤ entropyTargetDensity B M d * k →
      Real.log (((entropyHostDensityCutoff d * k : ℕ) : ℝ) / a) ≤
        (1 + 1 / 8192 : ℝ) * Real.log d ∧
      (1 - 1 / 8192 : ℝ) * Real.log d ≤
        Real.log (((entropyHostDensityCutoff d * k : ℕ) : ℝ) /
          ((a : ℝ) * (baselineBlockSize d * baselineBlockSize d : ℕ))) := by
  obtain ⟨d₁, hd₁⟩ := eventually_entropy_host_parameters B M
  have he := (entropyTypeLogError_tends_to_zero B M).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 8192 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp he
  refine ⟨max d₁ (Nat.ceil x₀), ?_⟩
  intro d hd k a ha haverage hdensity
  obtain ⟨hdlarge, hlog, hloglog, _, _, _⟩ := hd₁ d ((le_max_left _ _).trans hd)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans
    (by exact_mod_cast (le_max_right d₁ (Nat.ceil x₀)).trans hd)
  have herror := hx₀ d hx
  unfold entropyTypeLogError at herror
  have hsmall := (div_lt_iff₀ (show 0 < Real.log d by linarith)).mp herror
  have hK : 0 ≤ Real.log (entropyTypeLogConstant B M) := by
    apply Real.log_nonneg
    unfold entropyTypeLogConstant
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    nlinarith
  have hfour : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  obtain ⟨hupper, hlower⟩ := entropy_available_log_bounds B d k a M (by omega) ha hM
    (by linarith) hloglog haverage hdensity
  constructor <;> linarith

end Erdos911
