import Erdos911.PairMarkingParameters
import Erdos911.HereditaryDensity

namespace Erdos911

theorem exists_dense_connected_component_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) (hV : 0 < Fintype.card V)
    (haverage : a * Fintype.card V ≤ G.edgeSet.ncard) :
    ∃ c : G.ConnectedComponent, a * Nat.card c.supp ≤ (G.induce c.supp).edgeSet.ncard := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV
  by_contra hnone
  push Not at hnone
  have hsum := Finset.sum_lt_sum (fun c (_ : c ∈ (Finset.univ : Finset G.ConnectedComponent)) =>
    (hnone c).le) ⟨G.connectedComponentMk v, Finset.mem_univ _, hnone _⟩
  have hvertices : (∑ c : G.ConnectedComponent, (Nat.card c.supp : ℝ)) = Fintype.card V := by
    exact_mod_cast component_vertex_count_sum G
  have hedges : (∑ c : G.ConnectedComponent, ((G.induce c.supp).edgeSet.ncard : ℝ)) = G.edgeSet.ncard := by
    exact_mod_cast component_edge_count_sum G
  rw [← Finset.mul_sum, hvertices, hedges] at hsum
  linarith only [hsum, haverage]

/-- Simplicity forces a pair pattern meeting the required density
threshold to have at least d vertices. -/
theorem dense_pair_pattern_order {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d D : ℕ)
    (hd : 1 ≤ d) (hD : 2 ≤ D) (hV : 0 < Fintype.card V)
    (hdense : 32 * (Fintype.card V : ℝ) * Real.log D ≤ lightPairProbability d * F.edgeSet.ncard) :
    d ≤ Fintype.card V := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hk : (0 : ℝ) < Fintype.card V := by exact_mod_cast hV
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd6 : (d : ℝ) ≤ (d : ℝ) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hd1 (show 1 ≤ 6 by norm_num)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogD : (1 / 2 : ℝ) ≤ Real.log D := hlog2.trans
    (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hD))
  have hdeg : (2 : ℝ) * F.edgeSet.ncard ≤ (Fintype.card V : ℝ) ^ 2 := by
    have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => (F.degree_lt_card_verts v).le)
    rw [F.sum_degrees_eq_twice_card_edges, F.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
    have hn : 2 * F.edgeSet.ncard ≤ Fintype.card V * Fintype.card V := by simpa using hsum
    rw [pow_two]
    exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_right hdense (pow_nonneg hdp.le 6)
  have hcancel : (lightPairProbability d * F.edgeSet.ncard) * (d : ℝ) ^ 6 = F.edgeSet.ncard := by
    unfold lightPairProbability
    field_simp
  rw [hcancel] at hm
  have hlogmul := mul_le_mul_of_nonneg_left hlogD
    (show 0 ≤ 32 * (Fintype.card V : ℝ) * (d : ℝ) ^ 6 by positivity)
  have hlower : 16 * (Fintype.card V : ℝ) * (d : ℝ) ^ 6 ≤ F.edgeSet.ncard := by
    nlinarith only [hm, hlogmul]
  have hbound : (d : ℝ) ≤ Fintype.card V := by nlinarith only [hlower, hdeg, hd6, hk]
  exact_mod_cast hbound

theorem exists_dense_pair_component {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d D : ℕ)
    (hd : 1 ≤ d) (hD : 2 ≤ D) (hV : 0 < Fintype.card V)
    (hdense : (32 * Real.log D / lightPairProbability d) * Fintype.card V ≤ G.edgeSet.ncard) :
    ∃ c : G.ConnectedComponent, d ≤ Nat.card c.supp ∧
      32 * (Nat.card c.supp : ℝ) * Real.log D ≤
        lightPairProbability d * (G.induce c.supp).edgeSet.ncard := by
  classical
  have hρ : 0 < lightPairProbability d := by
    unfold lightPairProbability
    have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  obtain ⟨c, hc⟩ := exists_dense_connected_component_real G (32 * Real.log D / lightPairProbability d) hV hdense
  have hcomponent : 32 * (Nat.card c.supp : ℝ) * Real.log D ≤
      lightPairProbability d * (G.induce c.supp).edgeSet.ncard := by
    have hm := mul_le_mul_of_nonneg_left hc hρ.le
    have hcancel : lightPairProbability d *
        ((32 * Real.log D / lightPairProbability d) * Nat.card c.supp) =
        32 * (Nat.card c.supp : ℝ) * Real.log D := by field_simp
    rw [hcancel] at hm
    exact hm
  have hcard : 0 < Fintype.card c.supp := Fintype.card_pos_iff.mpr c.connected_toSimpleGraph.nonempty
  have hcomp' : 32 * (Fintype.card c.supp : ℝ) * Real.log D ≤
      lightPairProbability d * (G.induce c.supp).edgeSet.ncard := by
    simpa only [Nat.card_eq_fintype_card] using hcomponent
  exact ⟨c, by simpa only [Nat.card_eq_fintype_card] using dense_pair_pattern_order (G.induce c.supp) d D hd hD hcard hcomp', hcomponent⟩

end Erdos911
