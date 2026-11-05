import Erdos911.DictionaryEventIncidence
import Erdos911.DictionaryEventProbability
import Erdos911.RowCoordinateWeightBudget

open MeasureTheory

namespace Erdos911

theorem dictionaryRowEventWeight_max (q B : ℕ) (hq : 0 < q)
    (hscale : 8 * dictionaryLeftSize q * dictionaryLowDegree q ≤ q * B) :
    dictionaryRowEventWeight q B ≤ Real.exp (-(dictionaryLowDegree q : ℝ) / 128) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hap : (0 : ℝ) < dictionaryLeftSize q := by unfold dictionaryLeftSize; positivity
  have hs : 8 * (dictionaryLeftSize q : ℝ) * dictionaryLowDegree q ≤ (q : ℝ) * B := by exact_mod_cast hscale
  have hh : (dictionaryLowDegree q : ℝ) / 128 ≤ (q : ℝ) * B / (1024 * dictionaryLeftSize q) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    nlinarith only [hs]
  unfold dictionaryRowEventWeight
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul, neg_div] using neg_le_neg hh

theorem dictionaryRowEventWeight_half (q B : ℕ) (hq : 2 ^ 32 ≤ q)
    (hscale : 8 * dictionaryLeftSize q * dictionaryLowDegree q ≤ q * B) :
    dictionaryRowEventWeight q B ≤ 1 / 2 := by
  have hqpos : 0 < q := by norm_num at hq; omega
  have hq128 : 128 ≤ q := by norm_num at hq; omega
  have hp : q ≤ q ^ 50 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ q by omega) (by norm_num : 1 ≤ 50)
  have hD : (128 : ℝ) ≤ dictionaryLowDegree q := by
    have hn : 128 ≤ dictionaryLowDegree q := by unfold dictionaryLowDegree dictionaryDegreeCharge; omega
    exact_mod_cast hn
  have hlog : Real.log 2 ≤ (dictionaryLowDegree q : ℝ) / 128 := by
    linarith only [dictionary_log_two_bounds.2, hD]
  calc
    dictionaryRowEventWeight q B ≤ Real.exp (-(dictionaryLowDegree q : ℝ) / 128) :=
      dictionaryRowEventWeight_max q B hqpos hscale
    _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith only [hlog])
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num

theorem dictionary_coordinate_event_budget {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (hq : 2 ^ 32 ≤ q)
    (y : ↥(dictionaryLowVertices K (dictionaryLowDegree q))) :
    (∑ e ∈ (Finset.univ : Finset (DictionaryCoordinateEvent K q)).filter
      (fun e => y ∈ dictionaryCoordinateEventRows K q e),
      dictionaryRowEventWeight q (dictionaryCoordinateEventSize K q e)) ≤ dictionaryRowWeightBudget q := by
  classical
  have hqpos : 0 < q := by norm_num at hq; omega
  let T := (Finset.univ : Finset (DictionaryCoordinateEvent K q)).filter
    (fun e => y ∈ dictionaryCoordinateEventRows K q e)
  have hs : (∑ e ∈ T, dictionaryRowEventWeight q (dictionaryCoordinateEventSize K q e)) ≤
      T.card * Real.exp (-(dictionaryLowDegree q : ℝ) / 128) := by
    have hh := Finset.sum_le_sum (fun e (_ : e ∈ T) =>
      dictionaryRowEventWeight_max q (dictionaryCoordinateEventSize K q e) hqpos
        (dictionaryCoordinateEvent_scale_lower K q e))
    simpa only [Finset.sum_const, nsmul_eq_mul] using hh
  have hc : (T.card : ℝ) ≤ dictionaryRowEventCount q := by
    exact_mod_cast dictionaryCoordinateEvent_incidence_le K q hqpos y
  exact hs.trans ((mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans
    (row_coordinate_weight_sum_bound q hq))

theorem dictionary_event_correction_bound {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (hq : 0 < q)
    (e : DictionaryCoordinateEvent K q) :
    2 * dictionaryRowWeightBudget q * (dictionaryCoordinateEventRows K q e).card ≤
      (q : ℝ) * dictionaryCoordinateEventSize K q e / (1024 * dictionaryLeftSize q) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hap : (0 : ℝ) < dictionaryLeftSize q := by unfold dictionaryLeftSize; positivity
  have hΓp : (0 : ℝ) < dictionaryDegreeCharge q := by unfold dictionaryDegreeCharge; positivity
  have hη : 0 ≤ dictionaryRowWeightBudget q := by unfold dictionaryRowWeightBudget; positivity
  have hs : ((dictionaryCoordinateEventRows K q e).card : ℝ) ≤
      2 * dictionaryLeftSize q * dictionaryDegreeCharge q * dictionaryCoordinateEventSize K q e := by
    exact_mod_cast dictionaryCoordinateEventRows_card K q e
  calc
    _ ≤ 2 * dictionaryRowWeightBudget q *
        (2 * dictionaryLeftSize q * dictionaryDegreeCharge q * dictionaryCoordinateEventSize K q e) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (q : ℝ) * dictionaryCoordinateEventSize K q e / (2048 * dictionaryLeftSize q) := by
      unfold dictionaryRowWeightBudget
      field_simp
      ring
    _ ≤ (q : ℝ) * dictionaryCoordinateEventSize K q e / (1024 * dictionaryLeftSize q) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hh : 0 ≤ (q : ℝ) * dictionaryCoordinateEventSize K q e * dictionaryLeftSize q := by positivity
      nlinarith only [hh]

theorem dictionary_event_lll_probability {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (hq : 2 ^ 32 ≤ q)
    (e : DictionaryCoordinateEvent K q) :
    (uniformLabelMeasure ↥(dictionaryLowVertices K (dictionaryLowDegree q))
      (Fin (dictionaryWordLength q))).real (dictionaryCoordinateBadEvent K q e) ≤
        dictionaryRowEventWeight q (dictionaryCoordinateEventSize K q e) *
          Real.exp (-2 * (dictionaryRowWeightBudget q * (dictionaryCoordinateEventRows K q e).card)) := by
  have hqpos : 0 < q := by norm_num at hq; omega
  have hc := dictionary_event_correction_bound K q hqpos e
  apply (dictionaryCoordinateBadEvent_probability K q hq e).trans
  unfold dictionaryRowEventWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have heq : -(q : ℝ) * dictionaryCoordinateEventSize K q e / (512 * dictionaryLeftSize q) =
      -2 * ((q : ℝ) * dictionaryCoordinateEventSize K q e / (1024 * dictionaryLeftSize q)) := by ring
  rw [heq]
  simp only [neg_mul, neg_div]
  nlinarith only [hc]

end Erdos911
