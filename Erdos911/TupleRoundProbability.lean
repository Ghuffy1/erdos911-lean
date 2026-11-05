import Erdos911.TupleCenterParameters

open Filter

namespace Erdos911

noncomputable def tupleMarkRate (c b : ℝ) (t : ℕ) (D x : ℝ) : ℝ :=
  c / (D ^ t * x ^ b)

noncomputable def tupleRoundMean (c b : ℝ) (t : ℕ) (x : ℝ) : ℝ :=
  c / (2 * (4 : ℝ) ^ t) * x ^ (-(b * (t + 1 : ℕ)))

noncomputable def tupleSuccessRate (γ x : ℝ) : ℝ := x ^ (-γ)

theorem one_sub_exp_neg_ge_half (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hden : 0 < 1 + x := by linarith
  have hreciprocal : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hden (by linarith [Real.add_one_le_exp x])
  have hupper : 1 / (1 + x) ≤ 1 - x / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hx₀ (sub_nonneg.mpr hx₁)]
  linarith

theorem tupleMarkRate_mean (c b : ℝ) (t : ℕ) (D x : ℝ) (hD : 0 < D) (hx : 0 < x) :
    tupleMarkRate c b t D x * (((D / x ^ b) / 4) ^ t / 2) = tupleRoundMean c b t x := by
  have hpow : 0 < x ^ b := Real.rpow_pos_of_pos hx b
  unfold tupleMarkRate tupleRoundMean
  rw [Real.rpow_neg hx.le, Real.rpow_mul_natCast hx.le b (t + 1), pow_succ]
  simp only [div_pow]
  field_simp

theorem tupleMarkRate_bounds (c b : ℝ) (t : ℕ) (D x : ℝ)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1) (hb : 0 ≤ b) (hD : 1 ≤ D) (hx : 1 ≤ x) :
    0 < tupleMarkRate c b t D x ∧ tupleMarkRate c b t D x ≤ 1 := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpower : 1 ≤ D ^ t * x ^ b := by
    simpa only [one_mul] using mul_le_mul (one_le_pow₀ hD) (Real.one_le_rpow hx hb)
      (show (0 : ℝ) ≤ 1 by norm_num) (pow_nonneg hDpos.le t)
  refine ⟨div_pos hc₀ (mul_pos (pow_pos hDpos t) (Real.rpow_pos_of_pos hxpos b)), ?_⟩
  apply (div_le_iff₀ (show 0 < D ^ t * x ^ b by positivity)).mpr
  simpa only [one_mul] using hc₁.trans hpower

/-- A fixed power gap makes the useful tuple supply sufficient for the
chosen per-round success probability, uniformly in the host degree. -/
theorem tuple_round_parameters_uniform (c b γ : ℝ) (t : ℕ)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1) (hb : 0 < b) (hγ : b * (t + 1 : ℕ) < γ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ D ≥ (1 : ℝ),
      0 < tupleMarkRate c b t D x ∧ tupleMarkRate c b t D x ≤ 1 ∧
      0 < tupleSuccessRate γ x ∧
      tupleSuccessRate γ x ≤ 1 - Real.exp (-(tupleMarkRate c b t D x) *
        (((D / x ^ b) / 4) ^ t / 2)) := by
  let η := b * (t + 1 : ℕ)
  have hη : 0 < η := mul_pos hb (by positivity)
  have hgap : 0 < γ - η := sub_pos.mpr hγ
  have hmean : Tendsto (tupleRoundMean c b t) atTop (nhds 0) := by
    change Tendsto (fun x : ℝ => c / (2 * (4 : ℝ) ^ t) * x ^ (-η)) atTop (nhds 0)
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hη).const_mul (c / (2 * (4 : ℝ) ^ t))
  have hdecay := (tendsto_rpow_neg_atTop hgap).eventually
    (eventually_lt_nhds (show (0 : ℝ) < c / (4 * (4 : ℝ) ^ t) by positivity))
  have hsmall := hmean.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hdecay.and hsmall)
  refine ⟨max 1 x₀, ?_⟩
  intro x hx D hD
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  obtain ⟨hdecay, hsmall⟩ := hx₀ x ((le_max_right _ _).trans hx)
  obtain ⟨hp₀, hp₁⟩ := tupleMarkRate_bounds c b t D x hc₀ hc₁ hb.le hD hx1
  have hμ₀ : 0 ≤ tupleRoundMean c b t x := by
    unfold tupleRoundMean
    positivity
  have hsuccess : tupleSuccessRate γ x ≤ tupleRoundMean c b t x / 2 := by
    calc
      _ = x ^ (-(γ - η)) * x ^ (-η) := by
        unfold tupleSuccessRate
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
      _ ≤ (c / (4 * (4 : ℝ) ^ t)) * x ^ (-η) :=
        mul_le_mul_of_nonneg_right hdecay.le (Real.rpow_nonneg hxpos.le _)
      _ = tupleRoundMean c b t x / 2 := by unfold tupleRoundMean; dsimp only [η]; ring
  refine ⟨hp₀, hp₁, Real.rpow_pos_of_pos hxpos _, ?_⟩
  have hprob := hsuccess.trans (one_sub_exp_neg_ge_half _ hμ₀ hsmall.le)
  rw [← tupleMarkRate_mean c b t D x (by linarith) hxpos] at hprob
  simpa only [neg_mul] using hprob

theorem tuple_round_parameters_on_log (c b γ : ℝ) (t : ℕ)
    (hc₀ : 0 < c) (hc₁ : c ≤ 1) (hb : 0 < b) (hγ : b * (t + 1 : ℕ) < γ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D ≥ (1 : ℝ),
      0 < tupleMarkRate c b t D (Real.log d) ∧ tupleMarkRate c b t D (Real.log d) ≤ 1 ∧
      0 < tupleSuccessRate γ (Real.log d) ∧
      tupleSuccessRate γ (Real.log d) ≤ 1 - Real.exp (-(tupleMarkRate c b t D (Real.log d)) *
        (((D / (Real.log d) ^ b) / 4) ^ t / 2)) := by
  obtain ⟨x₀, hx₀⟩ := tuple_round_parameters_uniform c b γ t hc₀ hc₁ hb hγ
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually (eventually_ge_atTop x₀))
  refine ⟨Nat.ceil d₀, ?_⟩
  intro d hd D hD
  exact hx₀ (Real.log d) (hd₀ d ((Nat.le_ceil d₀).trans (by exact_mod_cast hd))) D hD

end Erdos911
