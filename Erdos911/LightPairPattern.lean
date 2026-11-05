import Erdos911.LightBandGap
import Erdos911.ReverseBandEntropy
import Erdos911.DensePairComponents

namespace Erdos911

/-- The light-pair case supplies a connected dense pattern, and the
corresponding host degree bound is independent of the left degree scale. -/
theorem exists_light_pair_pattern {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (S : B → Finset A) (d : ℕ) (M P : ℝ)
    (hd : 65536 ≤ d) (hM : 1 ≤ M) (hM2 : M ^ 2 ≤ d) (hP : (d : ℝ) ^ 200 ≤ P)
    (hA : 0 < Fintype.card A) (hrow : ∀ y, (S y).card = d)
    (hcolumn : ∀ x, P ≤ (incidenceColumn S x).card)
    (hfew : 2 * (heavyConcentratedRows S (P / (d : ℝ) ^ 12) (d / 4)).card ≤ Fintype.card B) :
    ∃ (n : ℕ) (j : Fin n)
      (c : (reverseCodegreeBand S (P / (d : ℝ) ^ 12) n j.val).ConnectedComponent),
      P / (d : ℝ) ^ 12 ≤ (2 : ℝ) ^ n ∧ (2 : ℝ) ^ n ≤ 2 * (P / (d : ℝ) ^ 12) ∧
      d ≤ Nat.card c.supp ∧
      32 * (Nat.card c.supp : ℝ) * Real.log (lightPairBaseDegree d M P n * 2 ^ j.val : ℕ) ≤
        lightPairProbability d *
          ((reverseCodegreeBand S (P / (d : ℝ) ^ 12) n j.val).induce c.supp).edgeSet.ncard := by
  classical
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdp : (0 : ℝ) < d := by linarith
  have hPpos : 0 < P := (pow_pos hdp 200).trans_le hP
  have hapos : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  let W := P / (d : ℝ) ^ 12
  have hW : 1 ≤ W := by
    have hp : (d : ℝ) ^ 12 ≤ P := (pow_le_pow_right₀ hd1 (by norm_num : 12 ≤ 200)).trans hP
    exact (le_div_iff₀ (pow_pos hdp 12)).mpr (by simpa only [one_mul] using hp)
  obtain ⟨n, hbase, hbaseup⟩ := exists_dyadic_enclosure W hW
  let D0 := lightPairBaseDegree d M P n
  obtain ⟨hD0, _, hD0up⟩ := light_pair_base_degree_bounds d M P n hd hM hM2 hP hbase
  have hgap := light_pair_entropy_gap d D0 hd hD0 hD0up
  let ρ := lightPairProbability d
  have hρ : 0 < ρ := by dsimp only [ρ, lightPairProbability]; positivity
  let C : ℝ := 32 * Fintype.card A / ρ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlogs : 0 ≤ Real.log D0 + Real.log 2 := by
    have h₁ : 0 ≤ Real.log D0 := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D0 by omega))
    have h₂ : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    linarith only [h₁, h₂]
  have hstep : 4 * (2 : ℝ) ^ n * C * (Real.log D0 + Real.log 2) ≤
      256 * P * Fintype.card A * (Real.log D0 + Real.log 2) / (d : ℝ) ^ 6 := by
    have hm := mul_le_mul_of_nonneg_right hbaseup (show 0 ≤ 4 * C * (Real.log D0 + Real.log 2) by positivity)
    have heq : (2 * W) * (4 * C * (Real.log D0 + Real.log 2)) =
        256 * P * Fintype.card A * (Real.log D0 + Real.log 2) / (d : ℝ) ^ 6 := by
      dsimp only [W, C, ρ, lightPairProbability]
      field_simp
      ring
    rw [heq] at hm
    nlinarith only [hm]
  have hstrict : 256 * P * Fintype.card A * (Real.log D0 + Real.log 2) / (d : ℝ) ^ 6 <
      P * Fintype.card A * d / 4 := by
    have hm := mul_lt_mul_of_pos_left hgap (show 0 < P * Fintype.card A / (4 * (d : ℝ) ^ 6) by positivity)
    have hleftEq : P * Fintype.card A / (4 * (d : ℝ) ^ 6) * (1024 * (Real.log D0 + Real.log 2)) =
        256 * P * Fintype.card A * (Real.log D0 + Real.log 2) / (d : ℝ) ^ 6 := by ring
    have hrightEq : P * Fintype.card A / (4 * (d : ℝ) ^ 6) * (d : ℝ) ^ 7 =
        P * Fintype.card A * d / 4 := by field_simp
    rw [hleftEq, hrightEq] at hm
    exact hm
  have hmass := light_incidence_weight_of_min_columns S W P d (by omega) hrow hcolumn hfew
  have hweight : 4 * (2 : ℝ) ^ n * C * (Real.log D0 + Real.log 2) <
      (orderedCodegreeWeight S (lightIncidenceGraph S W) : ℝ) := by
    have hmass' : P * Fintype.card A * d / 4 ≤
        (orderedCodegreeWeight S (lightIncidenceGraph S W) : ℝ) := by linarith only [hmass]
    exact (hstep.trans_lt hstrict).trans_le hmass'
  obtain ⟨j, hj⟩ := exists_dense_reverse_band S W C n D0 hbase hC (by omega) hweight
  let T := reverseCodegreeBand S W n j.val
  let D := D0 * 2 ^ j.val
  have hD : 2 ≤ D := by
    have hp : 1 ≤ 2 ^ j.val := Nat.one_le_pow _ _ (by norm_num)
    dsimp only [D]
    nlinarith only [hD0, hp]
  have haverage : (32 * Real.log D / lightPairProbability d) * Fintype.card A ≤ T.edgeSet.ncard := by
    have heq : (32 * Real.log D / lightPairProbability d) * Fintype.card A = C * Real.log D := by
      dsimp only [C, ρ]
      ring
    rw [heq]
    exact hj.le
  obtain ⟨c, horder, hdensity⟩ := exists_dense_pair_component T d D (by omega) hD hA haverage
  exact ⟨n, j, c, hbase, hbaseup, horder, hdensity⟩

end Erdos911
