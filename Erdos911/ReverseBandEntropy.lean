import Erdos911.CodegreeBandWeights
import Erdos911.DyadicEntropySums

namespace Erdos911

theorem reverse_band_ordered_weight_le {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (n j : ℕ) (hW : W ≤ (2 : ℝ) ^ n) :
    letI : DecidableRel (reverseCodegreeBand N W n j).Adj := Classical.decRel _
    (orderedCodegreeWeight N (reverseCodegreeBand N W n j) : ℝ) ≤
      2 * (2 : ℝ) ^ (n - j) * (reverseCodegreeBand N W n j).edgeSet.ncard := by
  classical
  apply orderedCodegreeWeight_le_edge_bound
  intro x z hxz
  exact_mod_cast (reverseCodegreeBand_bounds N W n j hW x z hxz).2.2.le

/-- If all reverse bands have small edge density, their total weighted
mass is bounded independently of the number of bands. -/
theorem reverse_band_entropy_bound {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W C : ℝ) (n D : ℕ) (hW : W ≤ (2 : ℝ) ^ n)
    (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hedges : ∀ j : Fin n, ((reverseCodegreeBand N W n j.val).edgeSet.ncard : ℝ) ≤
      C * Real.log (D * 2 ^ j.val : ℕ)) :
    letI : DecidableRel (lightIncidenceGraph N W).Adj := Classical.decRel _
    (orderedCodegreeWeight N (lightIncidenceGraph N W) : ℝ) ≤
      4 * (2 : ℝ) ^ n * C * (Real.log D + Real.log 2) := by
  classical
  let : ∀ j : Fin n, DecidableRel (reverseCodegreeBand N W n j.val).Adj := fun _ => Classical.decRel _
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hpoint (j : Fin n) :
      (orderedCodegreeWeight N (reverseCodegreeBand N W n j.val) : ℝ) ≤
        (2 * (2 : ℝ) ^ n * C) * ((1 / 2 : ℝ) ^ j.val * (Real.log D + Real.log 2 * j.val)) := by
    have hcount := reverse_band_ordered_weight_le N W n j.val hW
    have hscale := mul_le_mul_of_nonneg_left (hedges j)
      (show 0 ≤ 2 * (2 : ℝ) ^ (n - j.val) by positivity)
    have hlog : Real.log (D * 2 ^ j.val : ℕ) = Real.log D + Real.log 2 * j.val := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Real.log_mul hDpos.ne' (by positivity), Real.log_pow]
      ring
    calc
      _ ≤ 2 * (2 : ℝ) ^ (n - j.val) * (C * Real.log (D * 2 ^ j.val : ℕ)) := hcount.trans hscale
      _ = _ := by rw [reverse_dyadic_power n j.val j.isLt.le, hlog]; ring
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hpoint j)
  rw [← Finset.mul_sum] at hsum
  have hgeom := mul_le_mul_of_nonneg_left (dyadic_affine_sum_le n (Real.log D) (Real.log 2) hlogD hlog2)
    (show 0 ≤ 2 * (2 : ℝ) ^ n * C by positivity)
  have hpartition := reverseCodegreeBand_weight_partition N W n hW
  have hpartitionR : (orderedCodegreeWeight N (lightIncidenceGraph N W) : ℝ) =
      ∑ j : Fin n, (orderedCodegreeWeight N (reverseCodegreeBand N W n j.val) : ℝ) := by exact_mod_cast hpartition
  rw [hpartitionR]
  exact hsum.trans (by nlinarith only [hgeom])

theorem exists_dense_reverse_band {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W C : ℝ) (n D : ℕ) (hW : W ≤ (2 : ℝ) ^ n)
    (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hweight : letI : DecidableRel (lightIncidenceGraph N W).Adj := Classical.decRel _
      4 * (2 : ℝ) ^ n * C * (Real.log D + Real.log 2) <
        (orderedCodegreeWeight N (lightIncidenceGraph N W) : ℝ)) :
    ∃ j : Fin n, C * Real.log (D * 2 ^ j.val : ℕ) <
      ((reverseCodegreeBand N W n j.val).edgeSet.ncard : ℝ) := by
  classical
  by_contra h
  push Not at h
  exact (not_lt_of_ge (reverse_band_entropy_bound N W C n D hW hC hD h)) hweight

end Erdos911
