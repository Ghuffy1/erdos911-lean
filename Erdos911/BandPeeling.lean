import Erdos911.EdgeBands
import Erdos911.DegreeOrientedCut

namespace Erdos911

/-- Peeling every dyadic edge band has a total cost controlled by the
original vertex weights, rather than by the number of nonempty bands. -/
theorem exists_peeled_dyadic_bands {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (w : V → ℕ) (M : ℕ)
    (hM : ∀ v, w v ≤ M) (hpos : ∀ u v, F.Adj u v → 0 < min (w u) (w v))
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ J : Fin (Nat.log 2 M + 1) → SimpleGraph V,
      (∀ j, J j ≤ dyadicEdgeBand F w j.val) ∧
      (∀ j v, v ∈ (J j).support → c * (2 : ℝ) ^ j.val ≤ ((J j).neighborSet v).ncard) ∧
      (F.edgeSet.ncard : ℝ) ≤ (∑ j, ((J j).edgeSet.ncard : ℝ)) + 2 * c * ∑ v, (w v : ℝ) := by
  classical
  let N := Nat.log 2 M + 1
  let B : Fin N → SimpleGraph V := fun j => dyadicEdgeBand F w j.val
  have hpeel (j : Fin N) := exists_degree_peeling (B j) (fun _ => c * (2 : ℝ) ^ j.val)
    (fun _ => mul_nonneg hc (by positivity))
  choose J hJ hdegree hmass using hpeel
  let S : Fin N → Finset V := fun j => (Set.toFinite (B j).support).toFinset
  have hS : ∀ j v, v ∈ S j → 2 ^ j.val ≤ w v := by
    intro j v hv
    apply dyadicEdgeBand_support_lower F w hpos j.val v
    simpa only [S, Set.Finite.mem_toFinset] using hv
  have hsupport := dyadic_support_budget N S w hS
  have hcosteq : (∑ j : Fin N, supportWeight (B j) (fun _ => c * (2 : ℝ) ^ j.val)) =
      c * ∑ j : Fin N, ((S j).card : ℝ) * (2 : ℝ) ^ j.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [supportWeight, S, Finset.sum_const, nsmul_eq_mul]
    ring
  have hcost : (∑ j : Fin N, supportWeight (B j) (fun _ => c * (2 : ℝ) ^ j.val)) ≤
      2 * c * ∑ v, (w v : ℝ) := by
    rw [hcosteq]
    have h := mul_le_mul_of_nonneg_left hsupport hc
    nlinarith only [h]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hmass j)
  have htotal : (∑ j : Fin N, ((B j).edgeFinset.card : ℝ)) = F.edgeSet.ncard := by
    simp only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
    exact_mod_cast dyadicEdgeBand_partition F w M hM
  rw [htotal, Finset.sum_add_distrib] at hsum
  exact ⟨J, hJ, hdegree, hsum.trans (add_le_add le_rfl hcost)⟩

theorem dyadicEdgeBand_right_weight_bounds {V : Type*}
    (F : SimpleGraph V) (w : V → ℕ) (left right : Finset V)
    (hBip : F.IsBipartiteWith (left : Set V) (right : Set V))
    (horder : ∀ u ∈ left, ∀ v ∈ right, F.Adj u v → w v ≤ w u)
    (hpos : ∀ u v, F.Adj u v → 0 < min (w u) (w v))
    (j : ℕ) (v : V) (hv : v ∈ right) (hsupport : v ∈ (dyadicEdgeBand F w j).support) :
    2 ^ j ≤ w v ∧ w v < 2 * 2 ^ j := by
  obtain ⟨u, hvu⟩ := hsupport
  have hF := (dyadicEdgeBand_le F w j) hvu
  have hu : u ∈ left := hBip.symm.mem_of_mem_adj hv hF
  have hle : w v ≤ w u := horder u hu v hv hF.symm
  have h := dyadicEdgeBand_weight_bounds F w j v u hvu (hpos v u hF)
  simpa only [min_eq_left hle] using h

/-- The initial oriented cut followed by simultaneous band peeling
retains at least 7/32 of the original edges in total. -/
theorem exists_degree_oriented_peeled_bands {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (F : SimpleGraph V) (left right : Finset V), F ≤ G ∧
      F.IsBipartiteWith (left : Set V) (right : Set V) ∧
      ∃ J : Fin (Nat.log 2 G.maxDegree + 1) → SimpleGraph V,
        (∀ j, J j ≤ dyadicEdgeBand F (fun v => G.degree v) j.val) ∧
        (∀ j v, v ∈ (J j).support → (2 : ℝ) ^ j.val / 128 ≤ ((J j).neighborSet v).ncard) ∧
        (7 / 32 : ℝ) * G.edgeSet.ncard ≤ ∑ j, ((J j).edgeSet.ncard : ℝ) ∧
        (∀ j v, v ∈ right → v ∈ (J j).support →
          2 ^ j.val ≤ G.degree v ∧ G.degree v < 2 * 2 ^ j.val) := by
  classical
  obtain ⟨F, left, right, hFG, hBip, _, hmass, horder⟩ := exists_degree_oriented_bipartite_subgraph G
  let w := fun v => G.degree v
  have hpos : ∀ u v, F.Adj u v → 0 < min (w u) (w v) := by
    intro u v huv
    have hG := hFG huv
    exact lt_min (G.degree_pos_iff_exists_adj u |>.mpr ⟨v, hG⟩)
      (G.degree_pos_iff_exists_adj v |>.mpr ⟨u, hG.symm⟩)
  obtain ⟨J, hJ, hmin, hsum⟩ := exists_peeled_dyadic_bands F w G.maxDegree
    G.degree_le_maxDegree hpos (1 / 128) (by norm_num)
  have hdegreeSum : (∑ v, (w v : ℝ)) = 2 * G.edgeSet.ncard := by
    have h := G.sum_degrees_eq_twice_card_edges
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
    exact_mod_cast h
  rw [hdegreeSum] at hsum
  refine ⟨F, left, right, hFG, hBip, J, hJ, ?_, ?_, ?_⟩
  · intro j v hv
    have h := hmin j v hv
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using h
  · nlinarith only [hsum, hmass]
  · intro j v hv hvs
    apply dyadicEdgeBand_right_weight_bounds F w left right hBip horder hpos j.val v hv
    exact (J j).support_mono (hJ j) hvs

end Erdos911
