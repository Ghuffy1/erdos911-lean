import Erdos911.LightPairPattern
import Erdos911.LightHostBlueAvoidance
import Erdos911.IncidenceCopyRoles

namespace Erdos911

/-- The full light-pair branch of the strongly unbalanced incidence
argument, including arbitrary hosts and both color obstructions. -/
theorem light_pair_size_ramsey_lower_bound {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (S : R → Finset L) (d : ℕ) (M P : ℝ)
    (hd : 65536 ≤ d) (hM : 1 ≤ M) (hM2 : M ^ 2 ≤ d)
    (hP : (d : ℝ) ^ 200 ≤ P) (hL : 0 < Fintype.card L)
    (hrow : ∀ y, (S y).card = d)
    (hleft : ∀ x, P ≤ (incidenceColumn S x).card)
    (hmax : ∀ x, ((incidenceColumn S x).card : ℝ) ≤ (d : ℝ) ^ 4 * P)
    (hfew : 2 * (heavyConcentratedRows S (P / (d : ℝ) ^ 12) (d / 4)).card ≤ Fintype.card R) :
    (M * d) * (incidenceGraph S).edgeSet.ncard <
      (SimpleGraph.sizeRamsey (incidenceGraph S) (incidenceGraph S) : ℝ) := by
  classical
  have hdpos : 0 < d := by omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hPpos : 0 < P := (pow_pos hdp 200).trans_le hP
  have hR : 0 < Fintype.card R := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hL
    have hp : (0 : ℝ) < (incidenceColumn S x).card := hPpos.trans_le (hleft x)
    have hn : 0 < (incidenceColumn S x).card := by exact_mod_cast hp
    exact hn.trans_le (Finset.card_le_univ _)
  have heq : (incidenceGraph S).edgeSet.ncard = d * Fintype.card R := by
    rw [← Set.fintypeCard_eq_ncard, ← (incidenceGraph S).edgeFinset_card, incidenceGraph_edge_count]
    simp [hrow, mul_comm]
  have he : 0 < (incidenceGraph S).edgeSet.ncard := by rw [heq]; positivity
  have hleft' (x : L) : P ≤ (incidenceGraph S).degree (Sum.inl x) := by
    simpa only [incidenceGraph_degree_left, incidenceColumn] using hleft x
  have hmax' (x : L) : ((incidenceGraph S).degree (Sum.inl x) : ℝ) ≤ (d : ℝ) ^ 4 * P := by
    simpa only [incidenceGraph_degree_left, incidenceColumn] using hmax x
  obtain ⟨n, j, c, hbase, _, horder, hdense⟩ :=
    exists_light_pair_pattern S d M P hd hM hM2 hP hL hrow hleft hfew
  let Q := reverseCodegreeBand S (P / (d : ℝ) ^ 12) n j.val
  let F := Q.induce c.supp
  let t : ℕ := 2 ^ (n - (j.val + 1))
  let D0 := lightPairBaseDegree d M P n
  let D := D0 * 2 ^ j.val
  obtain ⟨hD0, hbasebudget, _⟩ := light_pair_base_degree_bounds d M P n hd hM hM2 hP hbase
  have hD : 2 ≤ D := by
    have hp : 1 ≤ 2 ^ j.val := Nat.one_le_pow _ _ (by norm_num)
    dsimp only [D, D0]
    nlinarith only [hD0, hp]
  have hpattern (u v : c.supp) (huv : F.Adj u v) : t ≤ incidenceCodegree S u.val v.val :=
    (reverseCodegreeBand_bounds S _ n j.val hbase u.val v.val huv).2.1
  have hF : F.Connected := c.connected_toSimpleGraph
  have horder' : d ≤ Fintype.card c.supp := by simpa only [Nat.card_eq_fintype_card] using horder
  have hdense' : 32 * (Fintype.card c.supp : ℝ) * Real.log D ≤
      lightPairProbability d * F.edgeSet.ncard := by
    simpa only [Nat.card_eq_fintype_card] using hdense
  obtain ⟨hDLlo, _, hDRlo, _, hDRsq, _, hDRP⟩ := light_host_cutoff_bounds d M P hd hM hM2 hP
  let DL := lightHostLeftCutoff d M P
  let DR := lightHostRightCutoff d M
  have hDLpos : 0 < DL := by
    have hh : (0 : ℝ) < DL := lt_of_lt_of_le (by positivity) hDLlo
    exact_mod_cast hh
  have hDRpos : 0 < DR := by
    have hh : (0 : ℝ) < DR := lt_of_lt_of_le (by positivity) hDRlo
    exact_mod_cast hh
  have hcutL : 16 * (M * d) * ((d : ℝ) ^ 4 * P) ≤ (DL : ℝ) := by
    convert hDLlo using 1
    ring
  have hcutR : 16 * (M * d) * d ≤ (DR : ℝ) := by
    convert hDRlo using 1
    ring
  have hΛ : M * d ≤ (d : ℝ) ^ 2 := by
    have hMd : M ≤ (d : ℝ) := by nlinarith only [hM2, hM, hd1]
    nlinarith only [mul_le_mul_of_nonneg_right hMd hdp.le]
  apply (sizeRamsey_real_gt_iff _ _ _).mpr
  intro k K hbudget
  let A := lightHostLeftRole K P DL
  let B := lightHostRightRole K DR
  let N := restrictedHostRows K A B
  have hAB : Disjoint A B := lightHostRoles_disjoint K P DL DR hDRP
  have hA (v : Fin k) (hv : v ∈ A) : K.degree v ≤ DL :=
    ((mem_lightHostLeftRole K P DL v).mp hv).2
  have hB (v : Fin k) (hv : v ∈ B) : K.degree v ≤ DR :=
    ((mem_lightHostRightRole K DR v).mp hv).2
  have hNrow (y : ↥B) : (N y).card ≤ DR :=
    (restrictedHostRows_row_bound K A B y).trans (hB y.val y.property)
  have hNcol (v : Fin k) : (incidenceColumn N v).card ≤ DL :=
    restrictedHostRows_column_bound K A B DL hA v
  have hNsquare (y : ↥B) : (N y).card ^ 2 ≤ 1024 * d ^ 5 := by
    have hh : ((N y).card : ℝ) ≤ DR := by exact_mod_cast hNrow y
    have hs := (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (N y).card) hh 2).trans hDRsq
    exact_mod_cast hs
  let U := heavyIncidenceGraph N (t : ℝ)
  have hU (v : Fin k) : U.degree v ≤ D :=
    reverse_band_host_degree N DL DR D0 n j.val j.isLt hNrow hNcol hbasebudget v
  obtain ⟨ω, havoid, hbad⟩ := exists_concrete_pair_marking F U hF D d hD hd hU horder' hdense' N hNsquare
  have hbadbudget : ((pairBadRows N d ω).card : ℝ) ≤
      (incidenceGraph S).edgeSet.ncard / (8 * d) := by
    have hBcard : (B.card : ℝ) ≤ 2 * (M * d) * (incidenceGraph S).edgeSet.ncard := by
      have hh : (B.card : ℝ) ≤ 2 * K.edgeSet.ncard := by exact_mod_cast lightHostRightRole_card_le K DR
      linarith only [hh, hbudget]
    have hb := pair_bad_row_budget d hd B.card ((incidenceGraph S).edgeSet.ncard) (M * d)
      hΛ (by positivity) hBcard
    have hbad' : ((pairBadRows N d ω).card : ℝ) ≤ (2 / (d : ℝ) ^ 8) * B.card := by
      simpa only [Fintype.card_coe] using hbad
    exact hbad'.trans hb
  refine ⟨pairHostRed K A B ω, pairHostRed_le K A B ω, ?_, ?_⟩
  · exact pair_host_red_excludes_target F S K A B hAB DR t P hDRP hleft'
      (fun y => Finset.card_pos.mp (by rw [hrow]; exact hdpos)) hB
      Subtype.val Subtype.val_injective (by dsimp only [t]; positivity) hpattern ω havoid
  · exact light_host_blue_excludes_target S d P ((d : ℝ) ^ 4 * P) (M * d) DL DR
      hdpos hDLpos hDRpos (by positivity) hDRP hrow hleft' hmax' he K hbudget hcutL hcutR ω hbadbudget

end Erdos911
