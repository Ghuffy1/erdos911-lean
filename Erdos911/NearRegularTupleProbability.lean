import Erdos911.TupleRoundProbability

namespace Erdos911

noncomputable def nearRegularLossPower : ℝ := 256 / 100000000

noncomputable def nearRegularCommonCutoff (D d : ℝ) : ℝ :=
  D / (Real.log d) ^ nearRegularLossPower

noncomputable def nearRegularTupleMarkRate (D d : ℝ) : ℝ :=
  tupleMarkRate (1 / 1024) nearRegularLossPower 128 D (Real.log d)

noncomputable def nearRegularRoundSuccess (d : ℝ) : ℝ :=
  tupleSuccessRate (1 / 256) (Real.log d)

theorem near_regular_tuple_probability_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ D ≥ (1 : ℝ),
      0 < nearRegularTupleMarkRate D d ∧ nearRegularTupleMarkRate D d ≤ 1 ∧
      0 < nearRegularRoundSuccess d ∧
      nearRegularRoundSuccess d ≤ 1 - Real.exp (-(nearRegularTupleMarkRate D d) *
        ((nearRegularCommonCutoff D d / 4) ^ 128 / 2)) := by
  obtain ⟨d₀, hd₀⟩ := tuple_round_parameters_on_log (1 / 1024) nearRegularLossPower (1 / 256) 128
    (by norm_num) (by norm_num) (by norm_num [nearRegularLossPower]) (by norm_num [nearRegularLossPower])
  exact ⟨d₀, hd₀⟩

theorem nearRegularRoundSuccess_pow (d : ℝ) (hlog : 0 < Real.log d) :
    nearRegularRoundSuccess d ^ 32 = (Real.log d) ^ (-1 / 8 : ℝ) := by
  unfold nearRegularRoundSuccess tupleSuccessRate
  rw [← Real.rpow_mul_natCast hlog.le (-(1 / 256 : ℝ)) 32]
  norm_num

end Erdos911
