import Erdos911.IncidencePairWeights
import Erdos911.HeavyIncidenceGeometry

namespace Erdos911

noncomputable def heavyIncidenceBall {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (x : L) : Finset L := by
  classical
  exact insert x (Finset.univ.filter (fun z => x ≠ z ∧ W ≤ (incidenceCodegree N x z : ℝ)))

theorem mem_heavyIncidenceBall {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (x z : L) :
    z ∈ heavyIncidenceBall N W x ↔ z = x ∨ (x ≠ z ∧ W ≤ incidenceCodegree N x z) := by
  classical
  simp only [heavyIncidenceBall, Finset.mem_insert, Finset.mem_filter,
    Finset.mem_univ, true_and]

noncomputable def lightIncidenceGraph {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) : SimpleGraph L where
  Adj x z := x ≠ z ∧ (incidenceCodegree N x z : ℝ) < W
  symm.symm x z h := ⟨h.1.symm, by simpa only [incidenceCodegree_symm N x z] using h.2⟩
  loopless.irrefl x h := h.1 rfl

theorem lightIncidenceGraph_adj {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (x z : L) :
    (lightIncidenceGraph N W).Adj x z ↔ x ≠ z ∧ (incidenceCodegree N x z : ℝ) < W := Iff.rfl

noncomputable def heavyConcentratedRows {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (q : ℕ) : Finset R := by
  classical
  exact Finset.univ.filter (fun y => ∃ x : L, q ≤ ((N y) ∩ heavyIncidenceBall N W x).card)

theorem light_row_neighbor_partition {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (y : R) (x : L) :
    letI : DecidableRel (lightIncidenceGraph N W).Adj := Classical.decRel _
    ((N y).filter (fun z => (lightIncidenceGraph N W).Adj x z)).card +
      ((N y) ∩ heavyIncidenceBall N W x).card = (N y).card := by
  classical
  have heq : (N y).filter (fun z => (lightIncidenceGraph N W).Adj x z) =
      N y \ heavyIncidenceBall N W x := by
    apply Finset.ext
    intro z
    simp only [Finset.mem_filter, Finset.mem_sdiff, mem_heavyIncidenceBall, lightIncidenceGraph_adj]
    by_cases h : x = z
    · simp [h]
    · simp [h, Ne.symm h, not_le]
  rw [heq]
  exact Finset.card_sdiff_add_card_inter _ _

/-- A row not concentrated in any heavy-pair ball contains many ordered
light pairs. The estimate is uniform in its neighborhood pattern. -/
theorem nonconcentrated_row_light_pairs {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (d : ℕ) (hd : 4 ≤ d) (y : R)
    (hrow : (N y).card = d) (hnot : y ∉ heavyConcentratedRows N W (d / 4)) :
    letI : DecidableRel (lightIncidenceGraph N W).Adj := Classical.decRel _
    d ^ 2 ≤ 2 * orderedRowPairCount N (lightIncidenceGraph N W) y := by
  classical
  have hball (x : L) : ((N y) ∩ heavyIncidenceBall N W x).card < d / 4 := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, Nat.le_of_not_gt h⟩)
  have hlocal (x : L) : d ≤ 2 * ((N y).filter (fun z => (lightIncidenceGraph N W).Adj x z)).card := by
    have hp := light_row_neighbor_partition N W y x
    have hb := hball x
    rw [hrow] at hp
    omega
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ N y) => hlocal x)
  simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hrow] at hsum
  change d * d ≤ 2 * orderedRowPairCount N (lightIncidenceGraph N W) y at hsum
  simpa only [pow_two] using hsum

/-- If at most half the rows are concentrated in heavy balls, the total
light-pair codegree mass is a fixed fraction of b*d^2. -/
theorem light_incidence_weight_lower {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (d : ℕ) (hd : 4 ≤ d)
    (hrow : ∀ y, (N y).card = d)
    (hfew : 2 * (heavyConcentratedRows N W (d / 4)).card ≤ Fintype.card R) :
    letI : DecidableRel (lightIncidenceGraph N W).Adj := Classical.decRel _
    Fintype.card R * d ^ 2 ≤ 4 * orderedCodegreeWeight N (lightIncidenceGraph N W) := by
  classical
  let E := heavyConcentratedRows N W (d / 4)
  let B := (Finset.univ : Finset R) \ E
  have hBcard : Fintype.card R ≤ 2 * B.card := by
    have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
    rw [Finset.card_univ] at hsplit
    change (Finset.univ \ E).card + E.card = Fintype.card R at hsplit
    change 2 * E.card ≤ Fintype.card R at hfew
    dsimp only [B]
    omega
  have hsum : B.card * d ^ 2 ≤ 2 * ∑ y ∈ B, orderedRowPairCount N (lightIncidenceGraph N W) y := by
    have hs := Finset.sum_le_sum (fun y (hy : y ∈ B) =>
      nonconcentrated_row_light_pairs N W d hd y (hrow y) (Finset.mem_sdiff.mp hy).2)
    simpa [Finset.sum_const, ← Finset.mul_sum] using hs
  have htotal : (∑ y ∈ B, orderedRowPairCount N (lightIncidenceGraph N W) y) ≤
      orderedCodegreeWeight N (lightIncidenceGraph N W) := by
    rw [orderedCodegreeWeight_eq_sum_rows]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun _ _ _ => Nat.zero_le _)
  have hmul := Nat.mul_le_mul_right (d ^ 2) hBcard
  nlinarith only [hmul, hsum, htotal]

/-- The lower bound in terms of the unbounded left degree scale P.
This is the weighted mass that forces a useful light codegree band. -/
theorem light_incidence_weight_of_min_columns {L R : Type*}
    [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W P : ℝ) (d : ℕ) (hd : 4 ≤ d)
    (hrow : ∀ y, (N y).card = d) (hcolumn : ∀ x, P ≤ (incidenceColumn N x).card)
    (hfew : 2 * (heavyConcentratedRows N W (d / 4)).card ≤ Fintype.card R) :
    letI : DecidableRel (lightIncidenceGraph N W).Adj := Classical.decRel _
    P * Fintype.card L * d ≤ 4 * (orderedCodegreeWeight N (lightIncidenceGraph N W) : ℝ) := by
  classical
  have hmass := light_incidence_weight_lower N W d hd hrow hfew
  have hmassR : (Fintype.card R : ℝ) * (d : ℝ) ^ 2 ≤
      4 * (orderedCodegreeWeight N (lightIncidenceGraph N W) : ℝ) := by exact_mod_cast hmass
  have hsum : (∑ x : L, (incidenceColumn N x).card) = d * Fintype.card R := by
    rw [sum_incidenceColumn_card]
    simp [hrow, mul_comm]
  have hcolumns : P * Fintype.card L ≤ (d : ℝ) * Fintype.card R := by
    calc
      _ = ∑ _x : L, P := by simp [mul_comm]
      _ ≤ ∑ x : L, ((incidenceColumn N x).card : ℝ) := Finset.sum_le_sum (fun x _ => hcolumn x)
      _ = _ := by exact_mod_cast hsum
  have hm := mul_le_mul_of_nonneg_right hcolumns (Nat.cast_nonneg (α := ℝ) d)
  nlinarith only [hm, hmassR]

end Erdos911
