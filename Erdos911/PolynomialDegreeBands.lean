import Erdos911.PolynomialRamsey
import Erdos911.SupportTransfer
import Erdos911.BandDegreeParameters

namespace Erdos911

/-- The low part of an arbitrary dyadic split is handled by the completed
polynomial maximum-degree theorem, with no local-density hypothesis. -/
theorem polynomial_degree_band_bound (A : ℕ) (M : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v ∈ G.support, (q : ℝ) / 65536 ≤ G.degree v) →
      (∀ v, (G.degree v : ℝ) ≤ (q : ℝ) ^ A + 2 * q) →
      (M * q) * G.edgeSet.ncard ≤ (SimpleGraph.sizeRamsey G G : ℝ) := by
  have hM' : 1 ≤ 131072 * M := by linarith
  obtain ⟨d₀, hd₀⟩ := polynomial_size_ramsey_lower_bound (A + 2) (131072 * M) hM'
  let N := max d₀ (max 1 (3 * 131072 ^ A))
  refine ⟨131072 * N, ?_⟩
  intro q hq V _ _ G _ hmin hmax
  classical
  have hN : N ≤ bandDegree q := by unfold bandDegree; omega
  have hd : d₀ ≤ bandDegree q := (le_max_left _ _).trans hN
  have hd1 : 1 ≤ bandDegree q := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hdcoef : 3 * 131072 ^ A ≤ bandDegree q := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hqbase : 131072 ≤ q := by omega
  have hbounds := bandDegree_bounds q hqbase
  have hq1 : 1 ≤ q := by omega
  have hqA : q ≤ q ^ A := by simpa using Nat.pow_le_pow_right hq1 hA
  have hqmax : q ^ A + 2 * q ≤ bandDegree q ^ (A + 2) := by
    have hp := Nat.pow_le_pow_left hbounds.2.2.1 A
    rw [Nat.mul_pow] at hp
    have hcoef : 3 * 131072 ^ A ≤ bandDegree q ^ 2 := by nlinarith only [hdcoef, hd1]
    have hmul := Nat.mul_le_mul_right (bandDegree q ^ A) hcoef
    rw [pow_add]
    nlinarith only [hp, hqA, hmul]
  have hmax' (v : V) : G.degree v ≤ bandDegree q ^ (A + 2) := by
    have hv : G.degree v ≤ q ^ A + 2 * q := by
      exact_mod_cast hmax v
    exact hv.trans hqmax
  by_cases he : 0 < G.edgeSet.ncard
  · let J := G.induce G.support
    have hcard := support_card_pos_of_edge_ncard_pos G he
    have hJmin (v : G.support) : bandDegree q ≤ J.degree v := by
      rw [degree_induce_support]
      have hfloor : (bandDegree q : ℝ) ≤ (q : ℝ) / 65536 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 65536)]
        exact_mod_cast Nat.div_mul_le_self q 65536
      exact_mod_cast hfloor.trans (hmin v.val v.property)
    have hJmax (v : G.support) : J.degree v ≤ bandDegree q ^ (A + 2) := by
      rw [degree_induce_support]
      exact hmax' v.val
    have hJ := hd₀ (bandDegree q) hd G.support J hcard hJmin hJmax
    have hmono : (SimpleGraph.sizeRamsey J J : ℝ) ≤ SimpleGraph.sizeRamsey G G := by
      exact_mod_cast sizeRamsey_mono ⟨SimpleGraph.Copy.induce G G.support⟩ ⟨SimpleGraph.Copy.induce G G.support⟩
    rw [show J.edgeSet.ncard = G.edgeSet.ncard from edge_ncard_induce_support G] at hJ
    have hqR : (q : ℝ) ≤ 131072 * bandDegree q := by exact_mod_cast hbounds.2.2.1
    have hm := mul_le_mul_of_nonneg_left hqR (show 0 ≤ M by linarith)
    have heR := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard)
    exact (by nlinarith only [heR] : (M * q) * G.edgeSet.ncard ≤
      ((131072 * M) * bandDegree q) * G.edgeSet.ncard).trans (hJ.le.trans hmono)
  · have hz : G.edgeSet.ncard = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero]
    positivity

end Erdos911
