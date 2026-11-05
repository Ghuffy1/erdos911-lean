import Erdos911.SeedAssignmentCounting
import Erdos911.GraphCounting

namespace Erdos911

def copyRetainedGraph {V W : Type*} {F : SimpleGraph V} {H : SimpleGraph W}
    (J : SimpleGraph W) (f : F.Copy H) : SimpleGraph V where
  Adj u v := F.Adj u v ∧ J.Adj (f u) (f v)
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := F.irrefl h.1

instance {V W : Type*} {F : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel F.Adj] (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) :
    DecidableRel (copyRetainedGraph J f).Adj := by
  unfold copyRetainedGraph
  infer_instance

theorem copyRetainedGraph_le {V W : Type*} {F : SimpleGraph V} {H : SimpleGraph W}
    (J : SimpleGraph W) (f : F.Copy H) : copyRetainedGraph J f ≤ F := fun _ _ h => h.1

theorem subgraph_degree_partition {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] (hR : R ≤ F) (v : V) :
    (F \ R).degree v + R.degree v = F.degree v := by
  have hsubset : R.neighborFinset v ⊆ F.neighborFinset v := by
    intro w hw
    exact (F.mem_neighborFinset v w).mpr (hR ((R.mem_neighborFinset v w).mp hw))
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sdiff]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_sdiff_add_card_eq_card hsubset

theorem subgraph_edge_partition {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] (hR : R ≤ F) :
    (F \ R).edgeFinset.card + R.edgeFinset.card = F.edgeFinset.card := by
  simpa only [SimpleGraph.edgeFinset_sdiff] using
    Finset.card_sdiff_add_card_eq_card (SimpleGraph.edgeFinset_mono hR)

noncomputable def exceptionalRoles {V : Type*} [Fintype V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] : Finset V := by
  classical
  exact Finset.univ.filter (fun v => 8 * R.degree v < 7 * F.degree v)

theorem exceptionalRoles_degree_sum {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] (hR : R ≤ F) :
    (∑ v ∈ exceptionalRoles F R, F.degree v) ≤ 16 * (F \ R).edgeFinset.card := by
  have hterm : ∀ v ∈ exceptionalRoles F R, F.degree v ≤ 8 * (F \ R).degree v := by
    intro v hv
    have hbad := (Finset.mem_filter.mp hv).2
    have hpartition := subgraph_degree_partition F R hR v
    omega
  calc
    _ ≤ ∑ v ∈ exceptionalRoles F R, 8 * (F \ R).degree v := Finset.sum_le_sum hterm
    _ ≤ ∑ v, 8 * (F \ R).degree v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = 8 * (∑ v, (F \ R).degree v) := (Finset.mul_sum ..).symm
    _ = 8 * (2 * (F \ R).edgeFinset.card) := by
      have hsum : (∑ v, (F \ R).degree v) = 2 * (F \ R).edgeFinset.card := by
        simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using
          (F \ R).sum_degrees_eq_twice_card_edges
      exact congrArg (8 * ·) hsum
    _ = 16 * (F \ R).edgeFinset.card := by omega

noncomputable def ordinaryRetainedEdges {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] : Finset (Sym2 V) :=
  R.edgeFinset \ incidentEdgesAtSet F (exceptionalRoles F R)

theorem ordinaryRetainedEdges_card {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] (hR : R ≤ F) :
    F.edgeFinset.card ≤ (ordinaryRetainedEdges F R).card + 17 * (F \ R).edgeFinset.card := by
  have hincident : (incidentEdgesAtSet F (exceptionalRoles F R)).card ≤
      16 * (F \ R).edgeFinset.card := by
    apply (show (incidentEdgesAtSet F (exceptionalRoles F R)).card ≤
      ∑ v ∈ exceptionalRoles F R, F.degree v from ?_).trans (exceptionalRoles_degree_sum F R hR)
    calc
      _ ≤ ∑ v ∈ exceptionalRoles F R, (F.incidenceFinset v).card := Finset.card_biUnion_le
      _ = _ := by simp
  have hsplit := Finset.card_le_card_sdiff_add_card
    (s := R.edgeFinset) (t := incidentEdgesAtSet F (exceptionalRoles F R))
  have hpartition := subgraph_edge_partition F R hR
  change F.edgeFinset.card ≤ (R.edgeFinset \ incidentEdgesAtSet F (exceptionalRoles F R)).card + _
  omega

noncomputable def ordinaryCopyAssignment {V W : Type*} [Fintype V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) : V → Option W := by
  classical
  exact fun v => if v ∈ exceptionalRoles F (copyRetainedGraph J f) then none else some (f v)

theorem ordinaryCopyAssignment_agrees {V W : Type*} [Fintype V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) :
    PartialAssignmentAgrees (ordinaryCopyAssignment J f) f := by
  classical
  intro v w h
  by_cases hv : v ∈ exceptionalRoles F (copyRetainedGraph J f)
  · simp only [ordinaryCopyAssignment, ite_eq_left hv, reduceCtorEq] at h
  · have hsome : some (f v) = some w := by
      simpa only [ordinaryCopyAssignment, ite_eq_right hv] using h
    exact Option.some.inj hsome

theorem ordinaryRetainedEdges_endpoints {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] (hR : R ≤ F)
    (u v : V) (h : s(u, v) ∈ ordinaryRetainedEdges F R) :
    R.Adj u v ∧ u ∉ exceptionalRoles F R ∧ v ∉ exceptionalRoles F R := by
  classical
  have hmem := Finset.mem_sdiff.mp h
  have huv : R.Adj u v := (R.mem_edgeFinset).mp hmem.1
  have hF := hR huv
  have hnot : ∀ x ∈ exceptionalRoles F R, ¬s(u, v) ∈ F.incidenceFinset x := by
    intro x hx he
    exact hmem.2 (Finset.mem_biUnion.mpr ⟨x, hx, he⟩)
  refine ⟨huv, ?_, ?_⟩
  · intro hu
    apply hnot u hu
    rw [F.incidenceFinset_eq_filter]
    simp [hF]
  · intro hv
    apply hnot v hv
    rw [F.incidenceFinset_eq_filter]
    simp [hF]

theorem ordinaryCopyAssignment_some {V W : Type*} [Fintype V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) (v : V)
    (hv : v ∉ exceptionalRoles F (copyRetainedGraph J f)) :
    ordinaryCopyAssignment J f v = some (f v) := by
  classical
  simp only [ordinaryCopyAssignment, ite_eq_right hv]

theorem ordinaryCopyAssignment_edge_count {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) :
    F.edgeFinset.card ≤ (partialAssignmentEdges F J (ordinaryCopyAssignment J f)).card +
      17 * (F \ copyRetainedGraph J f).edgeFinset.card := by
  classical
  let R := copyRetainedGraph J f
  let P := partialAssignmentEdges F J (ordinaryCopyAssignment J f)
  have hsub : (ordinaryRetainedEdges F R).image (Sym2.map (f : V → W)) ⊆
      P.map ⟨Subtype.val, Subtype.val_injective⟩ := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    induction a using Sym2.inductionOn with
    | hf u v =>
      obtain ⟨huv, hu, hv⟩ := ordinaryRetainedEdges_endpoints F R (copyRetainedGraph_le J f) u v ha
      exact Finset.mem_map.mpr ⟨⟨s(f u, f v), huv.2⟩,
        partialAssignmentEdges_of_adj F J (ordinaryCopyAssignment J f) u v (f u) (f v)
          huv.1 huv.2 (ordinaryCopyAssignment_some J f u hu) (ordinaryCopyAssignment_some J f v hv),
        rfl⟩
  have hcard : (ordinaryRetainedEdges F R).card ≤ P.card := by
    have hc := Finset.card_le_card hsub
    have hinj : Function.Injective (Sym2.map (f : V → W)) :=
      Sym2.map.injective (show Function.Injective (f : V → W) from f.injective)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_map] at hc
    exact hc
  have hmass := ordinaryRetainedEdges_card F R (copyRetainedGraph_le J f)
  exact hmass.trans (Nat.add_le_add_right hcard _)

theorem copyRetainedGraph_degree_eq {V W : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) (v : V) :
    (copyRetainedGraph J f).degree v =
      ((F.neighborFinset v).filter (fun u => J.Adj (f v) (f u))).card := by
  have hsets : (copyRetainedGraph J f).neighborFinset v =
      (F.neighborFinset v).filter (fun u => J.Adj (f v) (f u)) := by
    ext u
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    rfl
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hsets]

end Erdos911
