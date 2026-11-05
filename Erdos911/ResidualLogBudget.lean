import Erdos911.ResidualSamplingParameters

namespace Erdos911

theorem seedAssignmentCountBound_pos (k D s q : ℕ) (hk : 0 < k) (hD : 0 < D) :
    0 < seedAssignmentCountBound k D D s q := by
  unfold seedAssignmentCountBound
  positivity

theorem uniform_seed_assignment_event_log_bound (A d k D s q : ℕ) (C p : ℝ)
    (hd : 1 ≤ d) (hdk : d ≤ k) (hD : 1 ≤ D) (hDpow : D ≤ d ^ A)
    (hs : s ≤ k) (hseed : (s : ℝ) ≤ C * k * Real.log d / d)
    (hq : Real.log ((q : ℝ) + 1) ≤ 6 * Real.log (Real.log d))
    (hp : 0 < p) (hpd : 8 ≤ p * d) :
    Real.log (8 * seedAssignmentCountBound k D D s q / p) ≤
      (k : ℝ) * (6 * Real.log (Real.log d) +
        (((A : ℝ) + 3) * Real.log d + 4 +
          C * Real.log d * (4 * A * Real.log d + 1)) / d) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdkreal : (d : ℝ) ≤ k := by exact_mod_cast hdk
  have hratio : 1 ≤ (k : ℝ) / d := (one_le_div hdpos).mpr hdkreal
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hdreal
  have hcount := uniform_seed_assignment_log_bound A d k D s q C
    hd hdk hD hDpow hs hseed hq
  have hN : (0 : ℝ) < seedAssignmentCountBound k D D s q := by
    exact_mod_cast seedAssignmentCountBound_pos k D s q (by omega) (by omega)
  have hfrac : 8 / p ≤ (d : ℝ) := (div_le_iff₀ hp).mpr (by nlinarith)
  have hlogfrac : Real.log (8 / p) ≤ ((k : ℝ) / d) * Real.log d := by
    apply (Real.log_le_log (div_pos (by norm_num) hp) hfrac).trans
    nlinarith
  have hsplit : Real.log (8 * seedAssignmentCountBound k D D s q / p) =
      Real.log (seedAssignmentCountBound k D D s q) + Real.log (8 / p) := by
    rw [show 8 * (seedAssignmentCountBound k D D s q : ℝ) / p =
      (seedAssignmentCountBound k D D s q : ℝ) * (8 / p) by ring]
    exact Real.log_mul hN.ne' (div_pos (by norm_num) hp).ne'
  rw [hsplit]
  apply (add_le_add hcount hlogfrac).trans_eq
  field_simp
  ring

theorem baseline_residual_log_budget (A d D k b : ℕ) (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log d) (hloglog : 1 ≤ Real.log (Real.log d))
    (hdk : d ≤ k) (hD : d ≤ D) (hDpow : D ≤ d ^ A)
    (hα : baselineSampleRate A d ≤ 1 / 5) (herror : baselineResidualError A d ≤ 1)
    (hb : (d : ℝ) * k / 8 ≤ b) :
    Real.log (8 * seedAssignmentCountBound k D D (baselineSeedOrder A d k)
      (baselineBlockSize d) / baselineResidualRate d) ≤ baselineResidualRate d * b / 2 := by
  have hdpos : 0 < d := by omega
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hp : 0 < baselineResidualRate d := by
    unfold baselineResidualRate
    positivity
  have hpd : baselineResidualRate d * d = 256 * Real.log (Real.log d) := by
    unfold baselineResidualRate
    exact div_mul_cancel₀ _ hdreal.ne'
  obtain ⟨_, hseed, hs⟩ := baselineSeedOrder_bounds A d k hdpos hlog hdk hα
  have hseed' : (baselineSeedOrder A d k : ℝ) ≤
      (5 * baselineSampleConstant A) * k * Real.log d / d := by
    calc
      (baselineSeedOrder A d k : ℝ) ≤ 5 * baselineSampleRate A d * k := hseed
      _ = _ := by unfold baselineSampleRate; ring
  have hbound := uniform_seed_assignment_event_log_bound A d k D (baselineSeedOrder A d k)
    (baselineBlockSize d) (5 * baselineSampleConstant A) (baselineResidualRate d)
    hd hdk (by omega) hDpow hs hseed'
    (baselineBlockSize_log_bound d hlog hloglog) hp (by rw [hpd]; linarith)
  change Real.log _ ≤ (k : ℝ) *
    (6 * Real.log (Real.log d) + baselineResidualError A d) at hbound
  have hupper : (k : ℝ) * (6 * Real.log (Real.log d) + baselineResidualError A d) ≤
      7 * k * Real.log (Real.log d) := by
    have h := mul_le_mul_of_nonneg_left (show baselineResidualError A d ≤
      Real.log (Real.log d) by linarith) (Nat.cast_nonneg (α := ℝ) k)
    nlinarith only [h]
  have hlower : 16 * k * Real.log (Real.log d) ≤ baselineResidualRate d * b / 2 := by
    have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ baselineResidualRate d / 2 by positivity)
    have heq : baselineResidualRate d / 2 * ((d : ℝ) * k / 8) =
        16 * k * Real.log (Real.log d) := by
      calc
        baselineResidualRate d / 2 * ((d : ℝ) * k / 8) =
            (baselineResidualRate d * d) * k / 16 := by ring
        _ = _ := by rw [hpd]; ring
    rw [heq] at h
    nlinarith only [h]
  have hnonneg : 0 ≤ (k : ℝ) * Real.log (Real.log d) := by positivity
  exact hbound.trans (hupper.trans (by nlinarith only [hlower, hnonneg]))

end Erdos911
