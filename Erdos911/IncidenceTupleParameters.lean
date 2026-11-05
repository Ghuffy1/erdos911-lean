import Erdos911.NearRegularTupleProbability
import Erdos911.NearRegularStarBudget

namespace Erdos911

def incidenceTupleOrder (A : ℕ) : ℕ := 64 * (A + 1)

noncomputable def incidenceLossPower (A : ℕ) : ℝ :=
  1 / (65536 * ((incidenceTupleOrder A : ℝ) + 1))

noncomputable def incidenceCommonCutoff (A : ℕ) (P d : ℝ) : ℝ :=
  P / (Real.log d) ^ incidenceLossPower A

noncomputable def incidencePairCutoff (A : ℕ) (P d : ℝ) : ℝ :=
  incidenceCommonCutoff A P d / d ^ (1 / 16 : ℝ)

noncomputable def incidenceTupleMarkRate (A : ℕ) (P d : ℝ) : ℝ :=
  tupleMarkRate (1 / 1024) (incidenceLossPower A) (incidenceTupleOrder A) P (Real.log d)

theorem incidenceTupleOrder_pos (A : ℕ) : 0 < incidenceTupleOrder A := by
  unfold incidenceTupleOrder
  omega

theorem incidenceLossPower_pos (A : ℕ) : 0 < incidenceLossPower A := by
  unfold incidenceLossPower
  positivity

theorem incidenceLossPower_mul (A : ℕ) :
    incidenceLossPower A * ((incidenceTupleOrder A + 1 : ℕ) : ℝ) = 1 / 65536 := by
  unfold incidenceLossPower
  push_cast
  field_simp

theorem incidence_tuple_probability_uniform (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ P ≥ (1 : ℝ),
      0 < incidenceTupleMarkRate A P d ∧ incidenceTupleMarkRate A P d ≤ 1 ∧
      0 < nearRegularRoundSuccess d ∧
      nearRegularRoundSuccess d ≤ 1 - Real.exp (-(incidenceTupleMarkRate A P d) *
        ((incidenceCommonCutoff A P d / 4) ^ incidenceTupleOrder A / 2)) := by
  have hgap : incidenceLossPower A * ((incidenceTupleOrder A + 1 : ℕ) : ℝ) < 1 / 256 := by
    rw [incidenceLossPower_mul]
    norm_num
  obtain ⟨d₀, h⟩ := tuple_round_parameters_on_log (1 / 1024) (incidenceLossPower A) (1 / 256)
    (incidenceTupleOrder A) (by norm_num) (by norm_num) (incidenceLossPower_pos A) hgap
  exact ⟨d₀, h⟩

/-- The capacity calculation uses the local right-side degree cutoff,
while the tuple length may depend on the global host exponent. -/
theorem incidence_tuple_capacity_budget (A : ℕ) (d P Λ X m e : ℝ)
    (hlog : 0 < Real.log d) (hP : 0 < P) (hΛ : 0 < Λ) (hX : 0 ≤ X)
    (hvertices : X * incidenceCommonCutoff A P d ≤ 2 * m)
    (hhost : m ≤ Λ * e) (hcutoff : 16 * Λ * d ≤ P) :
    (2 * incidenceTupleMarkRate A P d) * 32 * X * P ^ incidenceTupleOrder A * d ≤ e / 128 := by
  have hz : 0 < (Real.log d) ^ incidenceLossPower A := Real.rpow_pos_of_pos hlog _
  have hPt : P ^ incidenceTupleOrder A ≠ 0 := pow_ne_zero _ hP.ne'
  have hnormalized : (2 * incidenceTupleMarkRate A P d) * 32 * X * P ^ incidenceTupleOrder A * d =
      X * d / (16 * (Real.log d) ^ incidenceLossPower A) := by
    unfold incidenceTupleMarkRate tupleMarkRate
    field_simp
    ring
  have hvertices' : X * P ≤ 2 * m * (Real.log d) ^ incidenceLossPower A := by
    apply (div_le_iff₀ hz).mp
    simpa only [incidenceCommonCutoff, mul_div_assoc] using hvertices
  have hhost' := mul_le_mul_of_nonneg_right hhost
    (show 0 ≤ 2 * (Real.log d) ^ incidenceLossPower A by positivity)
  have hcutoff' := mul_le_mul_of_nonneg_right hcutoff hX
  have hcharged : 8 * X * d ≤ e * (Real.log d) ^ incidenceLossPower A := by
    apply (mul_le_mul_iff_of_pos_left hΛ).mp
    nlinarith only [hvertices', hhost', hcutoff']
  rw [hnormalized]
  apply (div_le_div_iff₀ (show 0 < 16 * (Real.log d) ^ incidenceLossPower A by positivity)
    (show (0 : ℝ) < 128 by norm_num)).mpr
  nlinarith only [hcharged]

end Erdos911
