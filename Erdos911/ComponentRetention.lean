import Erdos911.ComponentStatistics
import Erdos911.CopyDensity

namespace Erdos911

theorem subgraph_component_edge_count_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    [Fintype G.ConnectedComponent] (hFG : F ≤ G) :
    (∑ c : G.ConnectedComponent, (F.induce c.supp).edgeSet.ncard) = F.edgeSet.ncard := by
  classical
  have hdegrees (c : G.ConnectedComponent) :
      (∑ v : c.supp, F.degree v.val) = 2 * (F.induce c.supp).edgeSet.ncard := by
    have hpoint (v : c.supp) : ((F.induce c.supp).neighborSet v).ncard =
        (F.neighborSet v.val).ncard := by
      have h := F.degree_induce_of_neighborSet_subset (s := c.supp) (v := v)
        (fun _ hw => c.mem_supp_of_adj_mem_supp v.property (hFG hw))
      simpa only [← SimpleGraph.ncard_neighborSet] using h
    calc
      _ = ∑ v : c.supp, (F.induce c.supp).degree v := by
        apply Finset.sum_congr rfl
        intro v _
        rw [← (F.induce c.supp).ncard_neighborSet, hpoint, F.ncard_neighborSet]
      _ = 2 * (F.induce c.supp).edgeFinset.card :=
        (F.induce c.supp).sum_degrees_eq_twice_card_edges
      _ = _ := by rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have hsum := Fintype.sum_fiberwise G.connectedComponentMk (fun v => F.degree v)
  change (∑ c : G.ConnectedComponent, ∑ v : c.supp, F.degree v.val) = ∑ v, F.degree v at hsum
  simp_rw [hdegrees] at hsum
  rw [← Finset.mul_sum, F.sum_degrees_eq_twice_card_edges, F.edgeFinset_card,
    Set.fintypeCard_eq_ncard] at hsum
  omega

/-- Small total loss and small bad-component mass leave a good component
retaining at least three quarters of its original edges. -/
theorem exists_good_retained_component {V : Type*} [Fintype V] [DecidableEq V]
    (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    [Fintype G.ConnectedComponent] (hFG : F ≤ G) (bad : G.ConnectedComponent → Prop)
    [DecidablePred bad] (he : 0 < G.edgeSet.ncard)
    (hkeep : (7 / 8 : ℝ) * G.edgeSet.ncard ≤ F.edgeSet.ncard)
    (hbad : (∑ c ∈ (Finset.univ : Finset G.ConnectedComponent).filter bad,
      ((G.induce c.supp).edgeSet.ncard : ℝ)) ≤ (G.edgeSet.ncard : ℝ) / 4) :
    ∃ c : G.ConnectedComponent, ¬bad c ∧
      (3 / 4 : ℝ) * (G.induce c.supp).edgeSet.ncard ≤ (F.induce c.supp).edgeSet.ncard := by
  classical
  by_contra hnot
  have hpoint (c : G.ConnectedComponent) : ((F.induce c.supp).edgeSet.ncard : ℝ) ≤
      (3 / 4 : ℝ) * (G.induce c.supp).edgeSet.ncard +
        (if bad c then ((G.induce c.supp).edgeSet.ncard : ℝ) / 4 else 0) := by
    by_cases hc : bad c
    · rw [ite_eq_left hc]
      have hm : ((F.induce c.supp).edgeSet.ncard : ℝ) ≤ (G.induce c.supp).edgeSet.ncard := by
        exact_mod_cast copy_edge_ncard_le (SimpleGraph.Copy.ofLE
          (F.induce c.supp) (G.induce c.supp) (fun _ _ h => hFG h))
      linarith
    · rw [ite_eq_right hc, add_zero]
      exact (lt_of_not_ge (fun h => hnot ⟨c, hc, h⟩)).le
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset G.ConnectedComponent)) => hpoint c)
  have hsumF : (∑ c : G.ConnectedComponent, ((F.induce c.supp).edgeSet.ncard : ℝ)) = F.edgeSet.ncard := by
    exact_mod_cast subgraph_component_edge_count_sum G F hFG
  have hsumG : (∑ c : G.ConnectedComponent, ((G.induce c.supp).edgeSet.ncard : ℝ)) = G.edgeSet.ncard := by
    exact_mod_cast component_edge_count_sum G
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumF, hsumG, ← Finset.sum_filter,
    ← Finset.sum_div] at hsum
  have heR : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast he
  nlinarith only [hsum, hkeep, hbad, heR]

end Erdos911
