import Erdos911.DictionaryUniformRows
import Erdos911.DisjointEventTails
import Mathlib.Data.Nat.Choose.Bounds

open MeasureTheory

namespace Erdos911

def dictionaryBadCoordinate {L C R : Type*} [Fintype C]
    (N : R → Finset L) (U : Finset R) (j : C) : Set ((L × C) → Bool) :=
  {ω | U.card < 4 * Fintype.card C * (eventHitSet (fun y => dictionaryUniformRow (N y) j) U ω).card}

theorem dictionaryBadCoordinate_depends {L C R : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C]
    (N : R → Finset L) (U : Finset R) (j : C) :
    DependsOnlyOn (dictionaryBadCoordinate N U j) (dictionaryRowCoordinates Finset.univ j) := by
  intro ω ω' heq hω
  have hA (y : R) (_ : y ∈ U) :
      DependsOnlyOn (dictionaryUniformRow (N y) j) (dictionaryRowCoordinates Finset.univ j) := by
    apply (dictionaryUniformRow_depends (N y) j).mono
    exact Finset.image_subset_image (Finset.subset_univ _)
  have hh := eventHitSet_eq_of_agreement (fun y => dictionaryUniformRow (N y) j) U _ hA ω ω' heq
  change U.card < 4 * Fintype.card C * (eventHitSet (fun y => dictionaryUniformRow (N y) j) U ω').card
  rw [← hh]
  exact hω

/-- One coordinate has too many uniform rows with probability at most
eight times the dictionary length times the single-row half-power. -/
theorem dictionaryBadCoordinate_probability {L C R : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C] [DecidableEq R]
    (N : R → Finset L) (U : Finset R) (s : ℕ) (hmin : ∀ y ∈ U, s ≤ (N y).card) (j : C) :
    (bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)).real
      (dictionaryBadCoordinate N U j) ≤ 8 * Fintype.card C * (1 / 2 : ℝ) ^ s := by
  classical
  let μ := bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)
  by_cases hU : U.Nonempty
  · have hu : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hU
    have hc : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
    let t : ℝ := U.card / (4 * Fintype.card C)
    have ht : 0 < t := by dsimp only [t]; positivity
    let A := fun y => dictionaryUniformRow (N y) j
    have hcover : dictionaryBadCoordinate N U j ⊆ {ω | t ≤ ((eventHitSet A U ω).card : ℝ)} := by
      intro ω hω
      have hh : (U.card : ℝ) < 4 * Fintype.card C * (eventHitSet A U ω).card := by exact_mod_cast hω
      apply (div_le_iff₀ (show (0 : ℝ) < 4 * Fintype.card C by positivity)).mpr
      nlinarith only [hh]
    have hsum : (∑ y ∈ U, μ.real (A y)) ≤ (2 * (1 / 2 : ℝ) ^ s) * U.card := by
      have hh := Finset.sum_le_sum (fun y hy => dictionaryUniformRow_probability_of_minimum (N y) j s (hmin y hy))
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hh
    have hm := finite_event_count_markov μ A U t ht
    calc
      μ.real (dictionaryBadCoordinate N U j) ≤ μ.real {ω | t ≤ ((eventHitSet A U ω).card : ℝ)} := measureReal_mono hcover
      _ ≤ (∑ y ∈ U, μ.real (A y)) / t := hm
      _ ≤ ((2 * (1 / 2 : ℝ) ^ s) * U.card) / t := div_le_div_of_nonneg_right hsum ht.le
      _ = 8 * Fintype.card C * (1 / 2 : ℝ) ^ s := by dsimp only [t]; field_simp; ring
  · have hz : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    have hempty : dictionaryBadCoordinate N U j = ∅ := by
      ext ω
      simp [dictionaryBadCoordinate, eventHitSet, hz]
    rw [hempty, measureReal_empty]
    positivity

/-- Independent dictionary coordinates give a uniform upper bound on
having at least J bad coordinates for any one row family. -/
theorem dictionary_bad_coordinates_tail {L C R : Type*}
    [Fintype L] [Fintype C] [DecidableEq L] [DecidableEq C] [DecidableEq R]
    (N : R → Finset L) (U : Finset R) (s J : ℕ) (hmin : ∀ y ∈ U, s ≤ (N y).card) :
    (bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)).real
      {ω | J ≤ (eventHitSet (dictionaryBadCoordinate N U) Finset.univ ω).card} ≤
        (8 * (Fintype.card C : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) ^ J := by
  classical
  let p : ℝ := 8 * Fintype.card C * (1 / 2 : ℝ) ^ s
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have ht := disjoint_coordinate_events_tail
    (fun _ : L × C => bernoulliMarginal (1 / 2) (by norm_num) (by norm_num))
    (dictionaryBadCoordinate N U) (dictionaryRowCoordinates (Finset.univ : Finset L))
    (dictionaryBadCoordinate_depends N U)
    (fun j k hjk => dictionaryRowCoordinates_disjoint _ _ j k hjk)
    Finset.univ J p hp (fun j _ => dictionaryBadCoordinate_probability N U s hmin j)
  have hchoose : (Nat.choose (Fintype.card C) J : ℝ) ≤ (Fintype.card C : ℝ) ^ J := by
    exact_mod_cast Nat.choose_le_pow (Fintype.card C) J
  have hm := mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp J)
  have ht' : (bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)).real
      {ω | J ≤ (eventHitSet (dictionaryBadCoordinate N U) Finset.univ ω).card} ≤
      (Nat.choose (Fintype.card C) J : ℝ) * p ^ J := by
    simpa only [Finset.card_univ, bitProductMeasure] using ht
  apply ht'.trans
  calc
    (Nat.choose (Fintype.card C) J : ℝ) * p ^ J ≤ (Fintype.card C : ℝ) ^ J * p ^ J := hm
    _ = (8 * (Fintype.card C : ℝ) ^ 2 * (1 / 2 : ℝ) ^ s) ^ J := by
      rw [← mul_pow]
      congr 1
      dsimp only [p]
      ring

end Erdos911
