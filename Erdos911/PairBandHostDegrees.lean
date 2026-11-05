import Erdos911.IncidenceCodegrees

namespace Erdos911

/-- A reverse-band threshold yields a host pair graph of degree at most
D0*2^j. The upper bound uses the local column and row degrees only. -/
theorem reverse_band_host_degree {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (DL DR D0 n j : ℕ) (hj : j < n)
    (hrow : ∀ y, (N y).card ≤ DR) (hcolumn : ∀ x, (incidenceColumn N x).card ≤ DL)
    (hbudget : 2 * (DL : ℝ) * DR ≤ (D0 : ℝ) * (2 : ℝ) ^ n) (x : L) :
    letI : DecidableRel (heavyIncidenceGraph N (2 ^ (n - (j + 1)) : ℕ)).Adj := Classical.decRel _
    (heavyIncidenceGraph N (2 ^ (n - (j + 1)) : ℕ)).degree x ≤ D0 * 2 ^ j := by
  classical
  let t := 2 ^ (n - (j + 1))
  let Q := heavyIncidenceGraph N (t : ℝ)
  have ht : (0 : ℝ) < t := by dsimp only [t]; positivity
  have hcharge := heavyIncidenceGraph_degree_charge N (t : ℝ) DR hrow x
  have hcol : ((incidenceColumn N x).card : ℝ) ≤ DL := by exact_mod_cast hcolumn x
  have hupper := mul_le_mul_of_nonneg_left hcol (Nat.cast_nonneg (α := ℝ) DR)
  have hpow : 2 * (t : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ n := by
    dsimp only [t]
    push_cast
    rw [mul_assoc, ← pow_add]
    have heq : n - (j + 1) + j = n - 1 := by omega
    rw [heq]
    have hn : n = (n - 1) + 1 := by omega
    conv_rhs => rw [hn, pow_succ]
    ring
  have hdegree : (Q.degree x : ℝ) ≤ (D0 : ℝ) * (2 : ℝ) ^ j := by
    have hm := congrArg (fun a : ℝ => (D0 : ℝ) * a) hpow
    nlinarith only [hcharge, hupper, hbudget, hm, ht]
  exact_mod_cast hdegree

end Erdos911
