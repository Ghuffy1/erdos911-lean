import Erdos911.BadComponentTypes
import Erdos911.IncidenceAveraging

namespace Erdos911

noncomputable def componentClass {V : Type*} [Fintype V] (G : SimpleGraph V) (k a : ℕ) :
    Finset (ComponentType G) := by
  classical
  exact Finset.univ.filter (fun t => componentOrder G t = k ∧ componentSize G t = a)

noncomputable def repeatedBadSupport {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (j : ℕ) (t : ComponentType G) : Finset (Sym2 W) := by
  classical
  exact H.edgeFinset.filter (fun e => ∃ f : (componentModel G t).Copy H,
    e ∈ copyRawEdges f ∧ 3 * j ≤ repeatedEdgeVolume P (copyRawEdges f))

theorem repeatedBadSupport_subset {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (j : ℕ) (t : ComponentType G) :
    repeatedBadSupport G H P j t ⊆ H.edgeFinset := by
  classical
  exact Finset.filter_subset _ _

theorem repeatedBadSupport_incidence_subset {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (k a j : ℕ) (e : Sym2 W) :
    ((componentClass G k a).filter (fun t => e ∈ repeatedBadSupport G H P j t)) ⊆
      repeatedBadTypes G H e.out.1 P k a j := by
  classical
  intro t ht
  obtain ⟨htclass, htsupport⟩ := Finset.mem_filter.mp ht
  obtain ⟨hk, ha⟩ := (Finset.mem_filter.mp htclass).2
  obtain ⟨f, hef, hrepeat⟩ := (Finset.mem_filter.mp htsupport).2
  have hroot : e.out.1 ∈ copyVertices f := by
    have hes := (mem_copyRawEdges_iff f e).mp hef
    have hv := SimpleGraph.Subgraph.mem_verts_of_mem_edge hes (Sym2.out_fst_mem e)
    rw [← copyVertices_eq_subgraph_verts f] at hv
    exact hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, ha, f, hroot, hrepeat⟩

/-- Many component types force one type to have a small total bad-copy
edge support. This is the finite averaging step of repeated-type pruning. -/
theorem exists_repeated_type_small_support_of_bounded {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (R : ℕ)
    (hP : BoundedEdgeBlocks P R) (k a j D M : ℕ)
    (hD : ∀ w, H.degree w ≤ D)
    (hM : ∀ U : Finset W, U.card = k → (H.induce (U : Set W)).edgeSet.ncard ≤ M)
    (hclass : (componentClass G k a).Nonempty) :
    ∃ t ∈ componentClass G k a,
      (repeatedBadSupport G H P j t).card * (componentClass G k a).card ≤
        H.edgeFinset.card *
          (D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j))) := by
  classical
  let C := D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j))
  have hincidence : ∀ e ∈ H.edgeFinset,
      ((componentClass G k a).filter (fun t => e ∈ repeatedBadSupport G H P j t)).card ≤ C := by
    intro e _
    exact (Finset.card_le_card (repeatedBadSupport_incidence_subset G H P k a j e)).trans
      (repeatedBadTypes_card_le_of_bounded G H e.out.1 P R hP k a j D M hD hM)
  obtain ⟨t, ht, hsmall⟩ := exists_small_incidence_fiber (componentClass G k a) H.edgeFinset
    (fun t e => e ∈ repeatedBadSupport G H P j t) hclass C hincidence
  have hfilter : H.edgeFinset.filter (fun e => e ∈ repeatedBadSupport G H P j t) =
      repeatedBadSupport G H P j t := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨repeatedBadSupport_subset G H P j t h, h⟩⟩
  rw [hfilter] at hsmall
  exact ⟨t, ht, hsmall⟩

theorem exists_repeated_type_small_support {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (q : ℕ) (ρ : ℝ)
    (hP : ValidBlockPacking H q ρ P) (k a j D M : ℕ)
    (hD : ∀ w, H.degree w ≤ D)
    (hM : ∀ U : Finset W, U.card = k → (H.induce (U : Set W)).edgeSet.ncard ≤ M)
    (hclass : (componentClass G k a).Nonempty) :
    ∃ t ∈ componentClass G k a,
      (repeatedBadSupport G H P j t).card * (componentClass G k a).card ≤
        H.edgeFinset.card *
          (D ^ (2 * (k - 1)) * ((M * (q * q)).choose j * M.choose (a - 2 * j))) := by
  exact exists_repeated_type_small_support_of_bounded G H P (q * q)
    hP.boundedEdgeBlocks k a j D M hD hM hclass

/-- Deleting the full bad-copy support eliminates every repeated-bad copy
of the selected component type, with badness measured in the original blocks. -/
theorem repeatedBadSupport_eliminates_bad_copies {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (j : ℕ) (t : ComponentType G)
    (hsize : 0 < componentSize G t) :
    ∀ f : (componentModel G t).Copy
        (H.deleteEdges (repeatedBadSupport G H P j t : Set (Sym2 W))),
      ¬ 3 * j ≤ repeatedEdgeVolume P (copyRawEdges
        ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) := by
  classical
  intro f hbad
  let J := H.deleteEdges (repeatedBadSupport G H P j t : Set (Sym2 W))
  let fH : (componentModel G t).Copy H :=
    (SimpleGraph.Copy.ofLE J H (H.deleteEdges_le _)).comp f
  have hnonempty : (componentModel G t).edgeSet.Nonempty :=
    (Set.ncard_pos (s := (componentModel G t).edgeSet)).mp hsize
  obtain ⟨a, ha⟩ := hnonempty
  let a' : (componentModel G t).edgeSet := ⟨a, ha⟩
  let e : Sym2 W := (f.mapEdgeSet a').val
  have heJ : e ∈ J.edgeSet := (f.mapEdgeSet a').property
  have heH : e ∈ H.edgeSet := by
    have he := heJ
    rw [H.edgeSet_deleteEdges] at he
    exact he.1
  have hecopy : e ∈ copyRawEdges fH := by
    apply Finset.mem_map.mpr
    refine ⟨fH.mapEdgeSet a', ?_, ?_⟩
    · apply Finset.mem_map.mpr
      exact ⟨a', Finset.mem_univ _, rfl⟩
    · rfl
  have heBad : e ∈ repeatedBadSupport G H P j t := by
    apply Finset.mem_filter.mpr
    exact ⟨(SimpleGraph.mem_edgeFinset).mpr heH, fH, hecopy, hbad⟩
  rw [H.edgeSet_deleteEdges] at heJ
  exact heJ.2 heBad

end Erdos911
