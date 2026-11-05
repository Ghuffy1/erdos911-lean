import Erdos911.DictionaryCoordinateEvents
import Erdos911.RowCoordinateTailBase

open MeasureTheory

namespace Erdos911

/-- Every row-coordinate bad event has an exponential tail at its own
dyadic scale. The integer threshold is a ceiling, with no rounding gap. -/
theorem dictionaryCoordinateBadEvent_probability {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (hq : 2 ^ 32 ≤ q)
    (e : DictionaryCoordinateEvent K q) :
    (uniformLabelMeasure ↥(dictionaryLowVertices K (dictionaryLowDegree q))
      (Fin (dictionaryWordLength q))).real (dictionaryCoordinateBadEvent K q e) ≤
        Real.exp (-(q : ℝ) * dictionaryCoordinateEventSize K q e / (512 * dictionaryLeftSize q)) := by
  classical
  let B := dictionaryCoordinateEventSize K q e
  let t := dictionaryRowThreshold q B
  let U := dictionaryCoordinateEventRows K q e
  let S := e.2.2.val
  have hqpos : 0 < q := by norm_num at hq; omega
  have hB : 0 < B := by dsimp only [B, dictionaryCoordinateEventSize]; positivity
  have ht : 0 < t := dictionaryRowThreshold_pos q B hqpos hB
  have hqp : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hap : (0 : ℝ) < dictionaryLeftSize q := by unfold dictionaryLeftSize; positivity
  have htp : (0 : ℝ) < t := by exact_mod_cast ht
  have htlo := dictionaryRowThreshold_lower q B
  have hBbound : (B : ℝ) ≤ 8 * dictionaryLeftSize q * t := by
    have hh : (B : ℝ) ≤ (t : ℝ) * (8 * (dictionaryLeftSize q : ℝ)) :=
      (div_le_iff₀ (show (0 : ℝ) < 8 * (dictionaryLeftSize q : ℝ) by positivity)).mp htlo
    nlinarith only [hh]
  have hU : (U.card : ℝ) ≤ 2 * dictionaryLeftSize q * dictionaryDegreeCharge q * B := by
    exact_mod_cast dictionaryCoordinateEventRows_card K q e
  have hsize : (U.card : ℝ) ≤ (16 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q) * t := by
    have hh := mul_le_mul_of_nonneg_left hBbound
      (show 0 ≤ 2 * (dictionaryLeftSize q : ℝ) * dictionaryDegreeCharge q by positivity)
    nlinarith only [hU, hh]
  have hprob := uniform_subset_hits_tail_ratio U S t
    (16 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q) ht (by positivity) hsize
  have hS : S.card ≤ dictionaryBadLimit q := (Finset.mem_filter.mp e.2.2.property).2
  have hbase : Real.exp 1 * (16 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q) * S.card /
      Fintype.card (Fin (dictionaryWordLength q)) ≤ Real.exp (-(q : ℝ) / 64) := by
    have hsR : (S.card : ℝ) ≤ dictionaryBadLimit q := by exact_mod_cast hS
    have hh := mul_le_mul_of_nonneg_left hsR
      (show 0 ≤ 16 * Real.exp 1 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q /
        dictionaryWordLength q by positivity)
    have hstep : Real.exp 1 * (16 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q) * S.card /
        Fintype.card (Fin (dictionaryWordLength q)) ≤
        16 * Real.exp 1 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q *
          dictionaryBadLimit q / dictionaryWordLength q := by
      rw [Fintype.card_fin]
      convert hh using 1 <;> ring
    exact hstep.trans (row_coordinate_tail_base q hq)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp 1 *
    (16 * (dictionaryLeftSize q : ℝ) ^ 2 * dictionaryDegreeCharge q) * S.card /
      Fintype.card (Fin (dictionaryWordLength q))) hbase t
  have hscale : Real.exp (-(q : ℝ) / 64) ^ t ≤ Real.exp (-(q : ℝ) * B / (512 * dictionaryLeftSize q)) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonpos_left htlo (show -(q : ℝ) / 64 ≤ 0 by linarith)
    convert hh using 1 <;> field_simp <;> ring
  exact hprob.trans (hpow.trans hscale)

end Erdos911
