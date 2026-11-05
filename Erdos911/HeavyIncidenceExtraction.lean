import Erdos911.HeavyPackingParameters

namespace Erdos911

/-- The heavy case contains a subtarget with polynomial-sized disjoint
left blocks, large right fibers, and a controlled edge loss. No Ramsey
bound for these blocks is assumed or asserted here. -/
theorem extract_heavy_incidence_blocks {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] [Nonempty L]
    (S : R → Finset L) (d : ℕ) (P : ℝ) (hd : 2 ^ 32 ≤ d)
    (hP : (d : ℝ) ^ 200 ≤ P) (hrow : ∀ y, (S y).card = d)
    (hleft : ∀ x, P ≤ (incidenceColumn S x).card)
    (hmax : ∀ x, ((incidenceColumn S x).card : ℝ) ≤ (d : ℝ) ^ 4 * P)
    (hmany : Fintype.card R ≤ 2 *
      (heavyConcentratedRows S (P / (d : ℝ) ^ 12) (heavyRowDegree d)).card) :
    ∃ (U : Finset R) (f : R → L) (N : R → Finset L),
      incidenceGraph N ≤ incidenceGraph S ∧
      (incidenceGraph S).edgeSet.ncard ≤ 128 * d ^ 34 * (incidenceGraph N).edgeSet.ncard ∧
      (∀ y ∈ U, (N y).card = heavyRowDegree d ∧
        N y ⊆ heavyIncidenceBall S (P / (d : ℝ) ^ 12) (f y)) ∧
      (∀ y ∉ U, N y = ∅) ∧
      (∀ y ∈ U, heavyRightMinimum d ≤ (U.filter (fun z => f z = f y)).card) ∧
      (∀ y ∈ U, ∀ z ∈ U, f y ≠ f z →
        Disjoint (heavyIncidenceBall S (P / (d : ℝ) ^ 12) (f y))
          (heavyIncidenceBall S (P / (d : ℝ) ^ 12) (f z))) ∧
      (∀ x, (heavyIncidenceBall S (P / (d : ℝ) ^ 12) x).card ≤ heavyRowDegree d ^ 20) := by
  classical
  have hd1 : 1 ≤ d := by norm_num at hd; omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hPpos : 0 < P := (pow_pos hdp 200).trans_le hP
  obtain ⟨hq, hdq, hcolors, hparameter, hballsize⟩ := heavy_packing_parameters d hd
  have hdegree (x : L) : (heavyIncidenceGraph S (P / (d : ℝ) ^ 12)).degree x ≤ d ^ 17 :=
    heavy_incidence_degree_bound S d P hd1 hPpos (fun y => (hrow y).le) hmax x
  obtain ⟨U, f, N, hmass, hsub, hNrow, hzero, hfiber, hdisjoint, hball⟩ :=
    exists_large_heavy_row_packing S (P / (d : ℝ) ^ 12) (heavyRowDegree d) (d ^ 17)
      (heavyRightMinimum d) hdegree hmany
  have hcolumnsum : (∑ x : L, ((incidenceColumn S x).card : ℝ)) = (d : ℝ) * Fintype.card R := by
    rw [← Nat.cast_sum, sum_incidenceColumn_card]
    simp [hrow, mul_comm]
  have hminmass : P * Fintype.card L ≤ (d : ℝ) * Fintype.card R := by
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset L)) => hleft x)
    rw [hcolumnsum] at hh
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hh
  have hparameterR0 : 4 * (heavyCenterColors d : ℝ) * heavyRightMinimum d * d ≤ (d : ℝ) ^ 200 := by
    exact_mod_cast hparameter
  have hparameterR : 4 * (heavyCenterColors d : ℝ) * heavyRightMinimum d * d ≤ P := hparameterR0.trans hP
  have hsmall : 4 * heavyCenterColors d * heavyRightMinimum d * Fintype.card L ≤ Fintype.card R := by
    have hh := (mul_le_mul_of_nonneg_right hparameterR
      (Nat.cast_nonneg (α := ℝ) (Fintype.card L))).trans hminmass
    have hR : 4 * (heavyCenterColors d : ℝ) * heavyRightMinimum d * Fintype.card L ≤ Fintype.card R := by
      nlinarith only [hh, hdp]
    exact_mod_cast hR
  have hmass' : Fintype.card R ≤ 4 * heavyCenterColors d * U.card :=
    large_heavy_row_mass _ _ _ _ _ hmass hsmall
  have hSedges : (incidenceGraph S).edgeSet.ncard = d * Fintype.card R := by
    rw [← Set.fintypeCard_eq_ncard, ← (incidenceGraph S).edgeFinset_card, incidenceGraph_edge_count]
    simp [hrow, mul_comm]
  have hNsize (y : R) : (N y).card = if y ∈ U then heavyRowDegree d else 0 := by
    by_cases hy : y ∈ U
    · simp only [hy, ite_true, (hNrow y hy).1]
    · simp only [hy, ite_false, hzero y hy, Finset.card_empty]
  have hNedges : (incidenceGraph N).edgeSet.ncard = heavyRowDegree d * U.card := by
    rw [← Set.fintypeCard_eq_ncard, ← (incidenceGraph N).edgeFinset_card, incidenceGraph_edge_count]
    simp_rw [hNsize]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  refine ⟨U, f, N, incidenceGraph_mono hsub, ?_, hNrow, hzero, hfiber, hdisjoint,
    fun x => (hball x).trans hballsize⟩
  rw [hSedges, hNedges]
  calc
    d * Fintype.card R ≤ d * (4 * heavyCenterColors d * U.card) := Nat.mul_le_mul_left _ hmass'
    _ ≤ (8 * heavyRowDegree d) * (4 * (4 * d ^ 34) * U.card) := by gcongr
    _ = 128 * d ^ 34 * (heavyRowDegree d * U.card) := by ring

end Erdos911
