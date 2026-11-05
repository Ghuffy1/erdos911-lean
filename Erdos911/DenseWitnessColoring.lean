import Erdos911.BlockRedConditions
import Erdos911.HostDegreePruning
import Erdos911.DeletedEdgeCapacity
import Erdos911.UnmarkedSetAvoidance

namespace Erdos911

/-- A connected dense test graph can be destroyed by a small set of host
edges. The average-degree condition is sufficient for the incidence bound. -/
theorem exists_dense_copy_hitting_marks {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (d D : ℕ) (hd : 4 ≤ d) (hdk : d ≤ Fintype.card V) (hD : 2 ≤ D)
    (haverage : d * Fintype.card V ≤ 2 * F.edgeFinset.card)
    (hhost : ∀ w, H.degree w ≤ D) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hscale : 32 * Real.log D ≤ p * d) :
    ∃ marked : Finset (Sym2 W), marked ⊆ H.edgeFinset ∧
      (marked.card : ℝ) ≤ 2 * p * H.edgeFinset.card ∧
      ¬F.IsContained (H.deleteEdges (marked : Set (Sym2 W))) := by
  classical
  have hdpos : 0 < d := by omega
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hweights := anchored_red_weight_bounds (Fintype.card V) F.edgeFinset.card d D p
    (hdpos.trans_le hdk) hdpos hdk hD haverage hp₀ (by linarith)
  have hparameters := inverse_degree_block_parameters d D p hd hD hscale
  obtain ⟨ω, hcost, hhits⟩ := exists_marks_meeting_sets
    (fun f : F.Copy H => copyHostEdges f) F.edgeFinset.card
    (Fintype.card V * D ^ (2 * (Fintype.card V - 1)))
    (fun f => (copyHostEdges_card F f).ge)
    (fun e => copy_edge_incidence_bound F H hF D hhost e)
    p (1 / d) hp₀ hp₁ hparameters.1 hweights.1
    (by simpa only [Nat.cast_mul, Nat.cast_pow] using hweights.2) hparameters.2
  let marked := (Finset.univ.filter (fun e : H.edgeSet => ω e = true)).map
    ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨marked, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp he
    exact H.mem_edgeFinset.mpr a.property
  · simpa only [marked, Finset.card_map, SimpleGraph.edgeFinset_card] using hcost
  · rintro ⟨f⟩
    let fH : F.Copy H := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
    obtain ⟨e, he, htrue⟩ := hhits fH
    have hecopy : e.val ∈ copyRawEdges fH := Finset.mem_map.mpr ⟨e, he, rfl⟩
    rw [copyRawEdges_ofLE_comp] at hecopy
    have heremains := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e.val).mp hecopy)
    rw [H.edgeSet_deleteEdges] at heremains
    exact heremains.2 (Finset.mem_map.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrue⟩, rfl⟩)

theorem copy_deleted_retained_partition {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : G.Copy H) :
    (copyRawEdges f ∩ (H \ J).edgeFinset).card + (retainedEdges J (copyRawEdges f)).card =
      G.edgeSet.ncard := by
  classical
  have heq : copyRawEdges f ∩ (H \ J).edgeFinset =
      (copyRawEdges f).filter (fun e => e ∉ J.edgeSet) := by
    ext e
    simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff,
      Set.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨he, _, hnot⟩
      exact ⟨he, hnot⟩
    · rintro ⟨he, hnot⟩
      exact ⟨he, f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e).mp he), hnot⟩
  rw [heq, retainedEdges_card_eq_filter]
  have h := Finset.card_filter_add_card_filter_not (s := copyRawEdges f)
    (fun e => e ∈ J.edgeSet)
  rw [copyRawEdges_card] at h
  omega

theorem degreePruned_copy_deleted_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (Δ D : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ) :
    ((copyRawEdges f ∩ (H \ degreePrunedGraph H D).edgeFinset).card : ℝ) ≤
      (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) := by
  have hretain := degreePruned_copy_retention G H f Δ D hΔ
  have hpartition : ((copyRawEdges f ∩ (H \ degreePrunedGraph H D).edgeFinset).card : ℝ) +
      (retainedEdges (degreePrunedGraph H D) (copyRawEdges f)).card = G.edgeSet.ncard := by
    exact_mod_cast copy_deleted_retained_partition G H (degreePrunedGraph H D) f
  linarith

/-- A dense connected subgraph of the target controls the full target's
size-Ramsey obstruction through the total number of marked edges. -/
theorem dense_witness_avoiding_coloring {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (G : SimpleGraph U) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hF : F.Connected) (hFG : F.IsContained G)
    (d Δ D : ℕ) (hd : 4 ≤ d) (hdk : d ≤ Fintype.card V) (hD : 2 ≤ D)
    (haverage : d * Fintype.card V ≤ 2 * F.edgeFinset.card)
    (hΔ : ∀ v, G.degree v ≤ Δ) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hscale : 32 * Real.log D ≤ p * d)
    (hbudget : (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) +
      2 * p * H.edgeFinset.card < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  let J := degreePrunedGraph H D
  have hJ : J ≤ H := degreePrunedGraph_le H D
  obtain ⟨marks, _, hcost, hfree⟩ := exists_dense_copy_hitting_marks F J hF d D hd hdk hD
    haverage (degreePrunedGraph_degree_le H D) p hp₀ hp₁ hscale
  let marked := (H \ J).edgeFinset ∪ marks
  have hbase : H.deleteEdges ((H \ J).edgeFinset : Set (Sym2 W)) = J := by
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_sdiff]
    exact H.deleteEdges_sdiff_eq_of_le hJ
  have hred : ¬F.IsContained (H.deleteEdges (marked : Set (Sym2 W))) := by
    have heq : H.deleteEdges (marked : Set (Sym2 W)) = J.deleteEdges (marks : Set (Sym2 W)) := by
      change H.deleteEdges (↑((H \ J).edgeFinset ∪ marks)) = _
      rw [Finset.coe_union, ← H.deleteEdges_deleteEdges, hbase]
    rw [heq]
    exact hfree
  apply avoiding_coloring_of_deleted_capacity F G H hFG marked hred
  intro g
  have hcapacity := degreePruned_copy_deleted_capacity G H g Δ D hΔ
  have hcard : (J.edgeFinset.card : ℝ) ≤ H.edgeFinset.card := by
    exact_mod_cast Finset.card_le_card (SimpleGraph.edgeFinset_mono hJ)
  have hcostH : (marks.card : ℝ) ≤ 2 * p * H.edgeFinset.card :=
    hcost.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
  have hunion : ((copyRawEdges g ∩ marked).card : ℝ) ≤
      (copyRawEdges g ∩ (H \ J).edgeFinset).card + marks.card := by
    exact_mod_cast copy_capacity_union (copyRawEdges g) (H \ J).edgeFinset marks
  have hstrict : ((copyRawEdges g ∩ marked).card : ℝ) < G.edgeSet.ncard := by
    linarith
  exact_mod_cast hstrict

end Erdos911
