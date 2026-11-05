import Erdos911.BandDegreeParameters
import Erdos911.CopyDensity

namespace Erdos911

theorem dyadic_band_upper_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : 0 < G.maxDegree)
    (j : Fin (Nat.log 2 G.maxDegree + 1)) : 2 ^ j.val ≤ G.maxDegree := by
  have hj : j.val ≤ Nat.log 2 G.maxDegree := by omega
  exact Nat.pow_le_of_le_log hG.ne' hj

theorem band_log_base_bound (d q : ℕ) (hd : 1 ≤ d) (hq : 131072 ≤ q)
    (hdq : d < 2 * q) (hlarge : 262144 ≤ bandDegree q) :
    Real.log d ≤ 2 * Real.log (bandDegree q) := by
  have hqd := (bandDegree_bounds q hq).2.2.1
  have hbase : (d : ℝ) ≤ 262144 * bandDegree q := by
    exact_mod_cast (show d ≤ 262144 * bandDegree q by omega)
  have hl : (262144 : ℝ) ≤ bandDegree q := by exact_mod_cast hlarge
  have hsquare : (d : ℝ) ≤ (bandDegree q : ℝ) ^ 2 := by nlinarith only [hbase, hl]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h := Real.log_le_log hdpos hsquare
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- A polynomial-size local density hypothesis passes to every band copy.
Only one extra power in the original cutoff is required. -/
theorem band_copy_local_density {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (F : SimpleGraph W) (f : F.Copy G)
    (B d q : ℕ) (C : ℝ) (hC : 0 ≤ C) (hd : 2 ≤ d)
    (hq : 131072 ≤ q) (hdq : d < 2 * q) (hlarge : 262144 ≤ bandDegree q)
    (hupper : q ≤ d ^ B)
    (hlocal : ∀ S : Finset V, S.card ≤ d ^ (B + 1) →
      ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) :
    ∀ S : Finset W, S.card ≤ 2 * nearRegularBlockSize (bandDegree q) →
      ((F.induce (S : Set W)).edgeSet.ncard : ℝ) ≤
        (2 * C) * Real.log (bandDegree q) * S.card := by
  have hqdegree := bandDegree_bounds q hq
  have hsize : 2 * nearRegularBlockSize (bandDegree q) ≤ d ^ (B + 1) := by
    have hb := (nearRegularBlockSize_bounds (bandDegree q) hqdegree.1).2.1
    have hmul := Nat.mul_le_mul_right (d ^ B) hd
    rw [pow_succ]
    nlinarith only [hb, hqdegree.2.1, hupper, hmul]
  have hcopied := induced_density_of_copy f (d ^ (B + 1)) (C * Real.log d) hlocal
  have hlogs := band_log_base_bound d q (by omega) hq hdq hlarge
  intro S hS
  apply (hcopied S (hS.trans hsize)).trans
  have h := mul_le_mul_of_nonneg_left hlogs hC
  have h' := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) S.card)
  nlinarith only [h']

end Erdos911
