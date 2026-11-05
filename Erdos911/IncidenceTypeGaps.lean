import Erdos911.IncidenceTypeRatios
import Erdos911.OrientationPruning
import Erdos911.TripleLogEntropy

open Filter

namespace Erdos911

noncomputable def orientationBadTypeLogBound (P k a e D : ℕ) (g : ℝ) : ℝ :=
  ((2 * (k - 1) : ℕ) : ℝ) * Real.log D + (k : ℝ) * Real.log 2 + Real.log ((e : ℝ) + 1) +
    (e : ℝ) * Real.log ((P * k : ℝ) / e) - g * Real.log ((k : ℝ) / a) + 2 * e

theorem orientationBadTypeBound_eq_exp (P k a e D : ℕ) (g : ℝ) (hD : 0 < D) :
    orientationBadTypeBound P k a e D g = Real.exp (orientationBadTypeLogBound P k a e D g) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hfirst : (D : ℝ) ^ (2 * (k - 1)) =
      Real.exp (((2 * (k - 1) : ℕ) : ℝ) * Real.log D) := by
    rw [Real.exp_nat_mul, Real.exp_log hDreal]
  have hsecond : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hthird : (e : ℝ) + 1 = Real.exp (Real.log ((e : ℝ) + 1)) :=
    (Real.exp_log (by positivity)).symm
  unfold orientationBadTypeBound orientationBadTypeLogBound
  rw [hfirst, hsecond, hthird, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  rw [Real.log_exp]
  congr 1
  ring

theorem incidenceTypeError_tends_to_zero (A : ℕ) :
    Tendsto (incidenceTypeError A) atTop (nhds 0) := by
  change Tendsto (fun x : ℝ => 64 * ((A : ℝ) + 1) * (Real.log x) ^ 2 / x) atTop (nhds 0)
  have h := ((isLittleO_log_rpow_rpow_atTop (2 : ℕ)
    (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero).const_mul (64 * ((A : ℝ) + 1))
  simpa only [incidenceTypeError, Real.rpow_natCast, Real.rpow_one,
    mul_div_assoc, mul_zero] using h

theorem incidence_entropy_margin_uniform (A : ℕ) (C δ : ℝ) (hδ : 0 < δ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      1 ≤ Real.log d ∧ 0 < Real.log (Real.log d) ∧
      Real.log (Real.log (Real.log d)) + C + incidenceTypeError A d ≤
        δ * Real.log (Real.log d) := by
  have hmain := (component_entropy_error_tends_to_zero C).comp Real.tendsto_log_atTop
  have hinv : Tendsto (fun x : ℝ => (Real.log (Real.log x))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have herror := (incidenceTypeError_tends_to_zero A).mul hinv
  have hsum : Tendsto (fun x : ℝ =>
      (Real.log (Real.log (Real.log x)) + C + incidenceTypeError A x) /
        Real.log (Real.log x)) atTop (nhds 0) := by
    have h := hmain.add herror
    simp only [add_zero, mul_zero] at h
    convert h using 1
    funext x
    simp only [Function.comp_def]
    ring
  have hsmall := hsum.eventually (eventually_lt_nhds hδ)
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hsmall.and hlogs)
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd
  obtain ⟨hsmall, hlog⟩ := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast hd))
  have hloglog : 0 < Real.log (Real.log d) := Real.log_pos (by linarith)
  refine ⟨by linarith, hloglog, ?_⟩
  exact ((div_lt_iff₀ hloglog).mp hsmall).le

theorem incidence_star_level_eq (A : ℕ) (d P : ℝ) (e : ℕ) (hP : 0 < P)
    (hlog : 0 < Real.log d) :
    (e : ℝ) / 128 * Real.log (P / incidenceCommonCutoff A P d) =
      (incidenceLossPower A / 128) * e * Real.log (Real.log d) := by
  have hp := Real.rpow_pos_of_pos hlog (incidenceLossPower A)
  have hratio : P / incidenceCommonCutoff A P d = (Real.log d) ^ incidenceLossPower A := by
    unfold incidenceCommonCutoff
    field_simp
  rw [hratio, Real.log_rpow hlog]
  ring

/-- All three incidence strips have an edge-count gap below the
triple-log component-class threshold. The orientation ratio is supplied
by the target's unequal bipartition. -/
theorem incidence_type_gaps (A : ℕ) (M τ : ℝ) (hM : 1 ≤ M) (hτ : 0 < τ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ k a e D P j : ℕ,
      d ≤ k → 0 < a → 0 < e → 0 < D → D ≤ d ^ A →
      (d : ℝ) * k ≤ 2 * e → (e : ℝ) ≤ (d : ℝ) * k →
      32 * M * (d : ℝ) ^ 2 ≤ (P : ℝ) → (P : ℝ) ≤ 64 * M * (d : ℝ) ^ 2 →
      τ * Real.log (Real.log d) ≤ Real.log ((k : ℝ) / a) →
      nearRegularLossFraction 1024 d * e / 32 ≤ (j : ℝ) →
      orientationBadTypeLogBound P k a e D ((e : ℝ) / 128) ≤
        (e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2) - e ∧
      starBadTypeLogBound (tolerantTupleOrder d) k e D P
        ((e : ℝ) / 128 * Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) ≤
        (e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2) - e ∧
      repeatedTypeExponent k e j D (P * k) (nearRegularBlockSize d * nearRegularBlockSize d) ≤
        (e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2) - e := by
  let δ := min (incidenceLossPower A / 128) (τ / 128)
  have hδ : 0 < δ := lt_min (div_pos (incidenceLossPower_pos A) (by norm_num)) (div_pos hτ (by norm_num))
  have hδstar : δ ≤ incidenceLossPower A / 128 := min_le_left _ _
  have hδorient : δ ≤ τ / 128 := min_le_right _ _
  have hbsmall : incidenceLossPower A ≤ 1 := by
    unfold incidenceLossPower
    apply (div_le_iff₀ (by positivity)).mpr
    have ht : (0 : ℝ) ≤ incidenceTupleOrder A := Nat.cast_nonneg _
    nlinarith only [ht]
  have hδsmall : δ ≤ 16 := by linarith
  obtain ⟨d₁, hd₁⟩ := incidence_entropy_margin_uniform A
    (Real.log (128 * M) + Real.log 256 + 10 + 3 * Real.log 2) δ hδ
  refine ⟨max 2 d₁, ?_⟩
  intro d hd k a e D P j hk ha he hD hDpow haverage hupper hlower hPlarge horient hj
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hd1 : 1 ≤ d := by omega
  have hkpos : 0 < k := by omega
  have hD1 : 1 ≤ D := by omega
  have hPpos : 0 < P := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h : (0 : ℝ) < P := (show 0 < 32 * M * (d : ℝ) ^ 2 by positivity).trans_le hlower
    exact_mod_cast h
  obtain ⟨hlog, hloglog, hmargin⟩ := hd₁ d ((le_max_right _ _).trans hd)
  have hlogpos : 0 < Real.log d := by linarith
  have havailable := incidence_available_log_upper M d k e P (by linarith) hd1 hkpos he hPpos haverage hPlarge
  have hmain := mul_le_mul_of_nonneg_left havailable (Nat.cast_nonneg (α := ℝ) e)
  have hoverhead := incidence_star_overhead A d k e D hd1 hD1 hDpow hlog haverage
  have hterm₁ : 0 ≤ ((tolerantTupleOrder d * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D ^ 2 + 1 by omega)))
  have hterm₂ : 0 ≤ (k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ D + 1 by omega)))
  have hroot : ((2 * (k - 1) : ℕ) : ℝ) * Real.log D ≤ (e : ℝ) * incidenceTypeError A d := by
    linarith only [hoverhead, hterm₁, hterm₂]
  have hcomparison : (e : ℝ) * (Real.log d + Real.log (128 * M) + 4 +
      incidenceTypeError A d - δ * Real.log (Real.log d)) ≤
        (e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2) - e := by
    have h := mul_le_mul_of_nonneg_left hmargin (Nat.cast_nonneg (α := ℝ) e)
    unfold tripleLogEntropyThreshold
    nlinarith only [h, Nat.cast_nonneg (α := ℝ) e]
  have hstar := incidence_star_level_eq A d P e (by exact_mod_cast hPpos) hlogpos
  have hstarpenalty : δ * e * Real.log (Real.log d) ≤
      (e : ℝ) / 128 * Real.log ((P : ℝ) / incidenceCommonCutoff A P d) := by
    rw [hstar]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδstar (Nat.cast_nonneg _)) hloglog.le
  have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hke : (k : ℝ) ≤ e := by
    have hdk := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ d by exact_mod_cast hd2) (Nat.cast_nonneg (α := ℝ) k)
    linarith only [hdk, haverage]
  have hlogcount : Real.log ((e : ℝ) + 1) ≤ e := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < e + 1 by positivity)
    linarith only [h]
  have horientextra : (k : ℝ) * Real.log 2 + Real.log ((e : ℝ) + 1) ≤ 2 * e := by
    have h := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (α := ℝ) k)
    linarith only [h, hke, hlogcount]
  have horientpenalty : δ * e * Real.log (Real.log d) ≤ (e : ℝ) / 128 * Real.log ((k : ℝ) / a) := by
    have h := mul_le_mul_of_nonneg_left horient (show 0 ≤ (e : ℝ) / 128 by positivity)
    have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδorient (Nat.cast_nonneg (α := ℝ) e)) hloglog.le
    nlinarith only [h, h']
  refine ⟨le_trans ?_ hcomparison, le_trans ?_ hcomparison, le_trans ?_ hcomparison⟩
  · unfold orientationBadTypeLogBound
    simp only [Nat.cast_mul] at hmain
    nlinarith only [hmain, hroot, horientextra, horientpenalty]
  · unfold starBadTypeLogBound
    simp only [Nat.cast_mul] at hmain
    nlinarith only [hmain, hoverhead, hstarpenalty, Nat.cast_nonneg (α := ℝ) e]
  · have hpair := incidence_pair_log_lower M d k e P hM hd1 hk he hupper hlower
    have hj' : 32 * (e : ℝ) * Real.log (Real.log d) ≤ (j : ℝ) * Real.log d := by
      have heq : nearRegularLossFraction 1024 d * e / 32 =
          (32 * (e : ℝ) * Real.log (Real.log d)) / Real.log d := by
        unfold nearRegularLossFraction
        ring
      rw [heq] at hj
      exact (div_le_iff₀ hlogpos).mp hj
    have hpair' := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg (α := ℝ) j)
    have hδU := mul_le_mul_of_nonneg_right hδsmall
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) e) hloglog.le)
    have hpenalty : δ * e * Real.log (Real.log d) ≤ (j : ℝ) *
        Real.log (((P * k : ℕ) : ℝ) / ((e : ℝ) * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ))) := by
      nlinarith only [hpair', hj', hδU]
    unfold repeatedTypeExponent
    nlinarith only [hroot, hmain, hpenalty, Nat.cast_nonneg (α := ℝ) e]

end Erdos911
