import Erdos911.BipartiteSplitPeeling

namespace Erdos911

theorem bipartite_of_le {V : Type*} (F G : SimpleGraph V) (hFG : F ≤ G)
    (left right : Set V) (hB : G.IsBipartiteWith left right) : F.IsBipartiteWith left right := by
  constructor
  · exact hB.disjoint
  · intro u v h
    exact hB.mem_of_adj (hFG h)

/-- The two left-degree classes retain a fixed total edge fraction.
The low class has bounded maximum degree; the high class has a left
degree gap and bounded right degree, ready for exact-degree normalization. -/
theorem exists_degree_threshold_split {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (q : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hmin : ∀ v, v ∈ G.support → (q : ℝ) / 128 ≤ G.degree v)
    (hright : ∀ v ∈ right, G.degree v ≤ 2 * q) :
    ∃ L H : SimpleGraph V, L ≤ G ∧ H ≤ G ∧
      L.IsBipartiteWith (left : Set V) (right : Set V) ∧
      H.IsBipartiteWith (left : Set V) (right : Set V) ∧
      (∀ v, v ∈ L.support → (q : ℝ) / 65536 ≤ (L.neighborSet v).ncard) ∧
      (∀ v, v ∈ H.support → (q : ℝ) / 65536 ≤ (H.neighborSet v).ncard) ∧
      (∀ v, ((L.neighborSet v).ncard : ℝ) ≤ T + 2 * q) ∧
      (∀ v ∈ left, v ∈ H.support → T / 8 < (H.neighborSet v).ncard) ∧
      (∀ v ∈ right, (H.neighborSet v).ncard ≤ 2 * q) ∧
      (3 / 4 : ℝ) * G.edgeSet.ncard ≤ (L.edgeSet.ncard : ℝ) + H.edgeSet.ncard := by
  classical
  let A := left.filter (fun v => (G.degree v : ℝ) ≤ T)
  have hA : A ⊆ left := Finset.filter_subset _ _
  obtain ⟨L, H, hL, hH, hlL, hlH, hrL, hrH, hmass⟩ :=
    exists_bipartite_split_peeling G left right A hB hA q hmin
  have hLG : L ≤ G := hL.trans G.between_le
  have hHG : H ≤ G := hH.trans G.between_le
  have hBL : L.IsBipartiteWith (left : Set V) (right : Set V) := bipartite_of_le L G hLG _ _ hB
  have hBH : H.IsBipartiteWith (left : Set V) (right : Set V) := bipartite_of_le H G hHG _ _ hB
  have hminL : ∀ v, v ∈ L.support → (q : ℝ) / 65536 ≤ (L.neighborSet v).ncard := by
    intro v hv
    obtain ⟨u, hvu⟩ := hv
    rcases hBL.mem_of_adj hvu with h | h
    · have hg := hmin v (L.support_mono hLG ⟨u, hvu⟩)
      have hp := hlL v h.1 ⟨u, hvu⟩
      have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      nlinarith only [hg, hp, hq]
    · exact hrL v h.1 ⟨u, hvu⟩
  have hminH : ∀ v, v ∈ H.support → (q : ℝ) / 65536 ≤ (H.neighborSet v).ncard := by
    intro v hv
    obtain ⟨u, hvu⟩ := hv
    rcases hBH.mem_of_adj hvu with h | h
    · have hg := hmin v (H.support_mono hHG ⟨u, hvu⟩)
      have hp := hlH v h.1 ⟨u, hvu⟩
      have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      nlinarith only [hg, hp, hq]
    · exact hrH v h.1 ⟨u, hvu⟩
  have hmaxL : ∀ v, ((L.neighborSet v).ncard : ℝ) ≤ T + 2 * q := by
    intro v
    by_cases hv : v ∈ L.support
    · obtain ⟨u, hvu⟩ := hv
      have hbase : (L.degree v : ℝ) ≤ G.degree v := by
        exact_mod_cast (SimpleGraph.Copy.ofLE L G hLG).degree_le v
      have hparts := (leftRestriction_bipartite G left right A hB hA).mem_of_adj (hL hvu)
      rcases hparts with h | h
      · have hthreshold : (G.degree v : ℝ) ≤ T := (Finset.mem_filter.mp h.1).2
        simpa only [L.ncard_neighborSet] using hbase.trans
          (hthreshold.trans (by linarith only [Nat.cast_nonneg (α := ℝ) q]))
      · have hr : (G.degree v : ℝ) ≤ 2 * q := by exact_mod_cast hright v h.1
        simpa only [L.ncard_neighborSet] using hbase.trans (hr.trans (by linarith only [hT]))
    · have hzero : L.degree v = 0 := (L.degree_eq_zero_iff_notMem_support v).mpr hv
      simp only [L.ncard_neighborSet, hzero, Nat.cast_zero]
      positivity
  have hgap : ∀ v ∈ left, v ∈ H.support → T / 8 < (H.neighborSet v).ncard := by
    intro v hv hvs
    obtain ⟨u, hvu⟩ := hvs
    have hparts := (leftRestriction_bipartite G left right (left \ A) hB Finset.sdiff_subset).mem_of_adj (hH hvu)
    have hvA : v ∉ A := by
      rcases hparts with h | h
      · exact (Finset.mem_sdiff.mp h.1).2
      · exact (Set.disjoint_left.mp hB.disjoint hv h.1).elim
    have hthreshold : T < (G.degree v : ℝ) := by
      apply lt_of_not_ge
      intro h
      exact hvA (Finset.mem_filter.mpr ⟨hv, h⟩)
    have hlow := hlH v hv ⟨u, hvu⟩
    linarith only [hthreshold, hlow]
  have hR : ∀ v ∈ right, (H.neighborSet v).ncard ≤ 2 * q := by
    intro v hv
    simpa only [H.ncard_neighborSet] using ((SimpleGraph.Copy.ofLE H G hHG).degree_le v).trans (hright v hv)
  exact ⟨L, H, hLG, hHG, hBL, hBH, hminL, hminH, hmaxL, hgap, hR, hmass⟩

end Erdos911
