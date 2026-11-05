import Erdos911.HeavyExtractionGain
import Erdos911.HeavyPairReduction

namespace Erdos911

/-- The large-right-block dictionary statement.
Its proof is large_right_block_ramsey_statement in LargeRightBlockRamsey. -/
def LargeRightBlockRamseyStatement : Prop :=
  ∃ q₀ : ℕ, ∀ q ≥ q₀,
    ∀ (L R : Type) [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
      (N : R → Finset L) (U : Finset R) (f : R → L) (X : L → Finset L),
      0 < (incidenceGraph N).edgeSet.ncard →
      (∀ y ∈ U, (N y).card = q ∧ N y ⊆ X (f y)) →
      (∀ y ∉ U, N y = ∅) →
      (∀ y ∈ U, 128 * q ^ 69 ≤ (U.filter (fun z => f z = f y)).card) →
      (∀ y ∈ U, ∀ z ∈ U, f y ≠ f z → Disjoint (X (f y)) (X (f z))) →
      (∀ x, (X x).card ≤ q ^ 20) →
      (7 / 16 : ℝ) * (q : ℝ) ^ 49 * (incidenceGraph N).edgeSet.ncard <
        (SimpleGraph.sizeRamsey (incidenceGraph N) (incidenceGraph N) : ℝ)

/-- The verified heavy-pair geometry reduces the heavy Ramsey branch
to the large-right-block dictionary proposition, including all losses. -/
theorem heavy_pairs_of_large_right_blocks (h : LargeRightBlockRamseyStatement) :
    HeavyPairRamseyStatement := by
  obtain ⟨q₀, hq₀⟩ := h
  intro M hM
  refine ⟨max (2 ^ 32) (max (4 * q₀) (Nat.ceil M)), ?_⟩
  intro d hd L R _ _ _ _ S P hL hP hrow hleft hmax hmany
  classical
  have hd32 : 2 ^ 32 ≤ d := (le_max_left _ _).trans hd
  have hdq : 4 * q₀ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdM : Nat.ceil M ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hMd : M ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hdM)
  have hqq₀ : q₀ ≤ heavyRowDegree d := by unfold heavyRowDegree; omega
  let : Nonempty L := Fintype.card_pos_iff.mp hL
  obtain ⟨U, f, N, hNS, hmass, hNrow, hzero, hfiber, hdisjoint, hball⟩ :=
    extract_heavy_incidence_blocks S d P hd32 hP hrow hleft hmax (le_of_lt hmany)
  have hdpos : 0 < d := by norm_num at hd32; omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hPpos : 0 < P := (pow_pos hdp 200).trans_le hP
  have hR : 0 < Fintype.card R := by
    obtain ⟨x⟩ := (inferInstance : Nonempty L)
    have hp : (0 : ℝ) < (incidenceColumn S x).card := hPpos.trans_le (hleft x)
    have hn : 0 < (incidenceColumn S x).card := by exact_mod_cast hp
    exact hn.trans_le (Finset.card_le_univ _)
  have hSedges : (incidenceGraph S).edgeSet.ncard = d * Fintype.card R := by
    rw [← Set.fintypeCard_eq_ncard, ← (incidenceGraph S).edgeFinset_card, incidenceGraph_edge_count]
    simp [hrow, mul_comm]
  have hSpos : 0 < (incidenceGraph S).edgeSet.ncard := by rw [hSedges]; positivity
  have hNpos : 0 < (incidenceGraph N).edgeSet.ncard := by
    by_contra hn
    have hz : (incidenceGraph N).edgeSet.ncard = 0 := by omega
    rw [hz, mul_zero] at hmass
    omega
  have hramsey := hq₀ (heavyRowDegree d) hqq₀ L R N U f
    (heavyIncidenceBall S (P / (d : ℝ) ^ 12)) hNpos hNrow hzero hfiber hdisjoint hball
  have hbudget : (M * d) * (incidenceGraph S).edgeSet.ncard ≤
      (7 / 16 : ℝ) * (heavyRowDegree d : ℝ) ^ 49 * (incidenceGraph N).edgeSet.ncard := by
    have hmassR : ((incidenceGraph S).edgeSet.ncard : ℝ) ≤
        (128 * (d : ℝ) ^ 34) * (incidenceGraph N).edgeSet.ncard := by exact_mod_cast hmass
    have h₁ := mul_le_mul_of_nonneg_left hmassR (show 0 ≤ M * (d : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (heavy_extraction_gain d M hd32 hMd)
      (Nat.cast_nonneg (α := ℝ) (incidenceGraph N).edgeSet.ncard)
    nlinarith only [h₁, h₂]
  have hmono : (SimpleGraph.sizeRamsey (incidenceGraph N) (incidenceGraph N) : ℝ) ≤
      SimpleGraph.sizeRamsey (incidenceGraph S) (incidenceGraph S) := by
    exact_mod_cast sizeRamsey_mono
      (show (incidenceGraph N).IsContained (incidenceGraph S) from ⟨SimpleGraph.Copy.ofLE _ _ hNS⟩)
      (show (incidenceGraph N).IsContained (incidenceGraph S) from ⟨SimpleGraph.Copy.ofLE _ _ hNS⟩)
  exact hbudget.trans_lt (hramsey.trans_le hmono)

/-- The exact conclusion from the large-right-block statement.
FullProof supplies the proved premise. -/
theorem exact_of_large_right_blocks (h : LargeRightBlockRamseyStatement) : ExactStatement :=
  exact_of_heavy_pairs (heavy_pairs_of_large_right_blocks h)

end Erdos911
