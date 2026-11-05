import Erdos911.BipartiteComponents
import Erdos911.IncidenceTypeRatios

namespace Erdos911

theorem bipartite_left_degree_ratio {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (d : ℕ) (hd : 0 < d)
    (q : ℝ) (hright : ∀ v ∈ right, G.degree v = d)
    (hleft : ∀ v ∈ left, (d : ℝ) * q ≤ G.degree v) :
    q * left.card ≤ right.card := by
  have hsum : (∑ v ∈ left, (G.degree v : ℝ)) = G.edgeSet.ncard := by
    have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hB
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
    exact_mod_cast h
  have hlower : (d : ℝ) * q * left.card ≤ G.edgeSet.ncard := by
    calc
      _ = ∑ _v ∈ left, (d : ℝ) * q := by simp [mul_comm]
      _ ≤ ∑ v ∈ left, (G.degree v : ℝ) := Finset.sum_le_sum hleft
      _ = _ := hsum
  have he := bipartite_exact_right_edge_count G left right hB d hright
  rw [he, Nat.cast_mul] at hlower
  exact (mul_le_mul_iff_of_pos_left (show (0 : ℝ) < d by exact_mod_cast hd)).mp
    (by simpa only [mul_assoc] using hlower)

theorem incidence_orientation_log_ratio (d τ : ℝ) (k a b : ℕ)
    (hlog : 0 < Real.log d) (ha : 0 < a) (hbk : b ≤ k)
    (hratio : (Real.log d) ^ τ * a ≤ (b : ℝ)) :
    τ * Real.log (Real.log d) ≤ Real.log ((k : ℝ) / a) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hpow : 0 < (Real.log d) ^ τ := Real.rpow_pos_of_pos hlog _
  have hratio' : (Real.log d) ^ τ ≤ (k : ℝ) / a := by
    apply (le_div_iff₀ haR).mpr
    exact hratio.trans (by exact_mod_cast hbk)
  have h := Real.log_le_log hpow hratio'
  simpa only [Real.log_rpow hlog] using h

theorem incidence_bipartite_size_bounds (k a b : ℕ) (q : ℝ)
    (hpartition : a + b = k) (hq : 1 ≤ q) (hratio : q * a ≤ (b : ℝ)) :
    a ≤ b ∧ k ≤ 2 * b := by
  have hscaled := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (α := ℝ) a)
  have hab : (a : ℝ) ≤ b := by linarith only [hscaled, hratio]
  have habNat : a ≤ b := by exact_mod_cast hab
  exact ⟨habNat, by omega⟩

end Erdos911
