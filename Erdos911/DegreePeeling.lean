import Erdos911.GraphCounting
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Max

namespace Erdos911

noncomputable def supportWeight {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : V → ℝ) : ℝ := by
  classical
  exact ∑ v ∈ (Set.toFinite G.support).toFinset, t v

theorem supportWeight_nonneg {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : V → ℝ) (ht : ∀ v, 0 ≤ t v) :
    0 ≤ supportWeight G t := by
  classical
  exact Finset.sum_nonneg (fun v _ => ht v)

theorem supportWeight_le_sum {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : V → ℝ) (ht : ∀ v, 0 ≤ t v) :
    supportWeight G t ≤ ∑ v, t v := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun v _ _ => ht v)

theorem supportWeight_delete_add_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : V → ℝ) (ht : ∀ v, 0 ≤ t v) (x : V)
    (hx : x ∈ G.support) :
    supportWeight (G.deleteIncidenceSet x) t + t x ≤ supportWeight G t := by
  classical
  unfold supportWeight
  have hsub : (Set.toFinite (G.deleteIncidenceSet x).support).toFinset ⊆
      (Set.toFinite G.support).toFinset.erase x := by
    intro v hv
    have hv' := G.support_deleteIncidenceSet_subset x (by simpa using hv)
    exact Finset.mem_erase.mpr ⟨by simpa only [Set.mem_singleton_iff] using hv'.2,
      by simpa using hv'.1⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => ht v)
  calc
    (∑ v ∈ (Set.toFinite (G.deleteIncidenceSet x).support).toFinset, t v) + t x ≤
        (∑ v ∈ (Set.toFinite G.support).toFinset.erase x, t v) + t x :=
      add_le_add hsum le_rfl
    _ = ∑ v ∈ (Set.toFinite G.support).toFinset, t v :=
      Finset.sum_erase_add _ _ (by simpa using hx)

/-- Delete vertices below their individual degree thresholds. The total lost
edge mass is bounded by the sum of the thresholds on the original support. -/
theorem exists_degree_peeling {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : V → ℝ) (ht : ∀ v, 0 ≤ t v) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ v ∈ H.support, t v ≤ ((H.neighborSet v).ncard : ℝ)) ∧
        (G.edgeFinset.card : ℝ) ≤ H.edgeSet.ncard + supportWeight G t := by
  classical
  let potential := fun H : SimpleGraph V => (H.edgeSet.ncard : ℝ) - supportWeight H t
  let graphs := Finset.univ.filter (fun H : SimpleGraph V => H ≤ G)
  have hnonempty : graphs.Nonempty := ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩⟩
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image graphs potential hnonempty
  have hHG : H ≤ G := (Finset.mem_filter.mp hH).2
  have hmin : ∀ v ∈ H.support, t v ≤ ((H.neighborSet v).ncard : ℝ) := by
    intro v hv
    by_contra hlow
    have hdegree : (H.degree v : ℝ) < t v := by
      simpa only [H.ncard_neighborSet] using lt_of_not_ge hlow
    have hdel : H.deleteIncidenceSet v ∈ graphs :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (H.deleteIncidenceSet_le v).trans hHG⟩
    have hmax' := hmax (H.deleteIncidenceSet v) hdel
    have hpenalty := supportWeight_delete_add_le H t ht v hv
    have hcount : ((H.deleteIncidenceSet v).edgeSet.ncard : ℝ) =
        (H.edgeSet.ncard : ℝ) - H.degree v := by
      have hdegreele := H.degree_le_card_edgeFinset v
      rw [← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card,
        H.card_edgeFinset_deleteIncidenceSet, Nat.cast_sub hdegreele]
      rw [H.edgeFinset_card, Set.fintypeCard_eq_ncard]
    change ((H.deleteIncidenceSet v).edgeSet.ncard : ℝ) -
      supportWeight (H.deleteIncidenceSet v) t ≤
        (H.edgeSet.ncard : ℝ) - supportWeight H t at hmax'
    rw [hcount] at hmax'
    linarith
  have hGmem : G ∈ graphs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hcompare := hmax G hGmem
  have hnonneg := supportWeight_nonneg H t ht
  have hGcount : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard]
  refine ⟨H, hHG, hmin, ?_⟩
  change (G.edgeSet.ncard : ℝ) - supportWeight G t ≤
    (H.edgeSet.ncard : ℝ) - supportWeight H t at hcompare
  rw [hGcount]
  linarith

theorem exists_min_degree_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (hd : 0 ≤ d) :
    ∃ (S : Set V) (H : SimpleGraph S), H.IsContained G ∧
      (∀ v, d ≤ ((H.neighborSet v).ncard : ℝ)) ∧
        (G.edgeFinset.card : ℝ) ≤ H.edgeSet.ncard + d * Fintype.card V := by
  classical
  obtain ⟨J, hJG, hdegree, hmass⟩ := exists_degree_peeling G (fun _ => d) (fun _ => hd)
  let H := J.induce J.support
  have hHJ : H.IsContained J := ⟨SimpleGraph.Copy.induce J J.support⟩
  have hHG : H.IsContained G := hHJ.trans ⟨SimpleGraph.Copy.ofLE J G hJG⟩
  have hcounts : H.edgeSet.ncard = J.edgeSet.ncard := by
    rw [← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card,
      ← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card]
    exact J.card_edgeFinset_induce_support
  refine ⟨J.support, H, hHG, ?_, ?_⟩
  · intro v
    have h := hdegree v.val v.property
    have hdeg : H.degree v = J.degree v :=
      J.degree_induce_of_neighborSet_subset (J.neighborSet_subset_support v.val)
    simpa only [H.ncard_neighborSet, hdeg, J.ncard_neighborSet] using h
  · have hcostG : supportWeight G (fun _ => d) ≤ d * Fintype.card V := by
      have h := supportWeight_le_sum G (fun _ => d) (fun _ => hd)
      simpa [mul_comm] using h
    rw [hcounts]
    linarith

theorem exists_density_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : ℝ) (hC : 0 ≤ C)
    (hdensity : C * Fintype.card V ≤ G.edgeFinset.card) :
    ∃ (S : Set V) (H : SimpleGraph S), H.IsContained G ∧
      (∀ v, C / 2 ≤ ((H.neighborSet v).ncard : ℝ)) ∧
        (G.edgeFinset.card : ℝ) / 2 ≤ H.edgeSet.ncard := by
  obtain ⟨S, H, hHG, hdegree, hmass⟩ :=
    exists_min_degree_subgraph G (C / 2) (by positivity)
  refine ⟨S, H, hHG, hdegree, ?_⟩
  nlinarith

end Erdos911
