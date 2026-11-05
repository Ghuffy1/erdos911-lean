import Erdos911.BandPeeling
import Erdos911.DegreeThresholdSplit
import Erdos911.DenseWitnessBound

namespace Erdos911

/-- The oriented dyadic reduction and left-degree split retain a fixed
total edge fraction without selecting only one degree band. -/
theorem exists_dyadic_threshold_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j) :
    ∃ (left right : Finset V)
      (L H : Fin (Nat.log 2 G.maxDegree + 1) → SimpleGraph V),
      (∀ j, L j ≤ G ∧ H j ≤ G) ∧
      (∀ j, (L j).IsBipartiteWith (left : Set V) (right : Set V) ∧
        (H j).IsBipartiteWith (left : Set V) (right : Set V)) ∧
      (∀ j v, v ∈ (L j).support → (2 : ℝ) ^ j.val / 65536 ≤ ((L j).neighborSet v).ncard) ∧
      (∀ j v, v ∈ (H j).support → (2 : ℝ) ^ j.val / 65536 ≤ ((H j).neighborSet v).ncard) ∧
      (∀ j v, (((L j).neighborSet v).ncard : ℝ) ≤ T j.val + 2 * (2 : ℝ) ^ j.val) ∧
      (∀ j v, v ∈ left → v ∈ (H j).support → T j.val / 8 < ((H j).neighborSet v).ncard) ∧
      (∀ j v, v ∈ right → ((H j).neighborSet v).ncard ≤ 2 * 2 ^ j.val) ∧
      (21 / 128 : ℝ) * G.edgeSet.ncard ≤
        ∑ j, (((L j).edgeSet.ncard : ℝ) + (H j).edgeSet.ncard) ∧
      ∀ j d, (∀ v, d ≤ G.degree v) →
        0 < (L j).edgeSet.ncard + (H j).edgeSet.ncard → d < 2 * 2 ^ j.val := by
  classical
  obtain ⟨F, left, right, hFG, hBip, J, hJ, hmin, hmass, hright⟩ := exists_degree_oriented_peeled_bands G
  let N := Nat.log 2 G.maxDegree + 1
  have hJG (j : Fin N) : J j ≤ G := ((hJ j).trans (dyadicEdgeBand_le F _ j.val)).trans hFG
  have hJF (j : Fin N) : J j ≤ F := (hJ j).trans (dyadicEdgeBand_le F _ j.val)
  have hJB (j : Fin N) : (J j).IsBipartiteWith (left : Set V) (right : Set V) :=
    bipartite_of_le (J j) F (hJF j) _ _ hBip
  have hright' (j : Fin N) (v : V) (hv : v ∈ right) : (J j).degree v ≤ 2 * 2 ^ j.val := by
    by_cases hs : v ∈ (J j).support
    · exact ((SimpleGraph.Copy.ofLE (J j) G (hJG j)).degree_le v).trans ((hright j v hv hs).2.le)
    · rw [(SimpleGraph.degree_eq_zero_iff_notMem_support (J j) v).mpr hs]
      exact Nat.zero_le _
  have hex (j : Fin N) := exists_degree_threshold_split (J j) left right (hJB j) (2 ^ j.val)
    (T j.val) (hT j.val) (by
      intro v hv
      simpa only [Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hmin j v hv)
    (hright' j)
  choose L H hL hH hBL hBH hmL hmH hmaxL hgap hmaxH hsum using hex
  refine ⟨left, right, L, H, ?_, ?_, ?_, ?_, ?_, hgap, hmaxH, ?_, ?_⟩
  · intro j
    exact ⟨(hL j).trans (hJG j), (hH j).trans (hJG j)⟩
  · intro j
    exact ⟨hBL j, hBH j⟩
  · intro j v hv
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmL j v hv
  · intro j v hv
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmH j v hv
  · intro j v
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hmaxL j v
  · have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hsum j)
    rw [← Finset.mul_sum] at h
    have hmass' := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 3 / 4 by norm_num)
    nlinarith only [h, hmass']
  · intro j d hd hnonzero
    have hpos : ∀ u v, F.Adj u v → 0 < min (G.degree u) (G.degree v) := by
      intro u v huv
      exact lt_min ((G.degree_pos_iff_exists_adj u).mpr ⟨v, hFG huv⟩)
        ((G.degree_pos_iff_exists_adj v).mpr ⟨u, (hFG huv).symm⟩)
    apply dyadicEdgeBand_minimum_scale F (fun v => G.degree v) j.val d hd hpos
    by_cases hLpos : 0 < (L j).edgeSet.ncard
    · exact hLpos.trans_le (copy_edge_ncard_le
        (SimpleGraph.Copy.ofLE _ _ ((hL j).trans (hJ j))))
    · have hHpos : 0 < (H j).edgeSet.ncard := by omega
      exact hHpos.trans_le (copy_edge_ncard_le
        (SimpleGraph.Copy.ofLE _ _ ((hH j).trans (hJ j))))

end Erdos911
