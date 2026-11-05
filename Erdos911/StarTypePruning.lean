import Erdos911.StarBadTypes
import Erdos911.RepeatedTypePruning

namespace Erdos911

noncomputable def starBadSupport {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s P : ℕ) (L : ℝ) (t : ComponentType G) : Finset (Sym2 W) := by
  classical
  exact H.edgeFinset.filter (fun e => ∃ f : (componentModel G t).Copy H,
    e ∈ copyRawEdges f ∧ IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P L)

theorem starBadSupport_subset {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s P : ℕ) (L : ℝ) (t : ComponentType G) : starBadSupport G H J s P L t ⊆ H.edgeFinset := by
  classical
  exact Finset.filter_subset _ _

theorem starBadSupport_incidence_subset {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s k a P : ℕ) (L : ℝ) (e : Sym2 W) :
    ((componentClass G k a).filter (fun t => e ∈ starBadSupport G H J s P L t)) ⊆
      starBadTypes G H J e.out.1 s k a P L := by
  classical
  intro t ht
  obtain ⟨htclass, htsupport⟩ := Finset.mem_filter.mp ht
  obtain ⟨hk, ha⟩ := (Finset.mem_filter.mp htclass).2
  obtain ⟨f, hef, hbad⟩ := (Finset.mem_filter.mp htsupport).2
  have hroot : e.out.1 ∈ copyVertices f := by
    have he := (mem_copyRawEdges_iff f e).mp hef
    have hv := SimpleGraph.Subgraph.mem_verts_of_mem_edge he (Sym2.out_fst_mem e)
    rw [← copyVertices_eq_subgraph_verts f] at hv
    exact hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, ha, f, hroot, hbad⟩

theorem exists_star_type_small_support {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s k a D P : ℕ) (L : ℝ) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k a).Nonempty) :
    ∃ t ∈ componentClass G k a,
      ((starBadSupport G H J s P L t).card : ℝ) * (componentClass G k a).card ≤
        H.edgeFinset.card * starBadTypeBound s k a D P L := by
  classical
  have hincidence : ∀ e ∈ H.edgeFinset,
      (((componentClass G k a).filter (fun t => e ∈ starBadSupport G H J s P L t)).card : ℝ) ≤
        starBadTypeBound s k a D P L := by
    intro e _
    have hsubset := Finset.card_le_card (starBadSupport_incidence_subset G H J s k a P L e)
    have hreal : (((componentClass G k a).filter
        (fun t => e ∈ starBadSupport G H J s P L t)).card : ℝ) ≤
        (starBadTypes G H J e.out.1 s k a P L).card := by exact_mod_cast hsubset
    exact hreal.trans (starBadTypes_card_bound G H J e.out.1 s k a D P L ha hP hD hlocal)
  obtain ⟨t, ht, hsmall⟩ := exists_small_incidence_fiber_real (componentClass G k a) H.edgeFinset
    (fun t e => e ∈ starBadSupport G H J s P L t) hclass (starBadTypeBound s k a D P L) hincidence
  have hfilter : H.edgeFinset.filter (fun e => e ∈ starBadSupport G H J s P L t) =
      starBadSupport G H J s P L t := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨starBadSupport_subset G H J s P L t h, h⟩⟩
  rw [hfilter] at hsmall
  exact ⟨t, ht, hsmall⟩

theorem starBadSupport_eliminates_bad_copies {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (s P : ℕ) (L : ℝ) (t : ComponentType G)
    (hsize : 0 < componentSize G t) :
    ∀ f : (componentModel G t).Copy
        (H.deleteEdges (starBadSupport G H J s P L t : Set (Sym2 W))),
      ¬IsStarDeficitImage H J
        (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
        (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) s P L := by
  classical
  intro f hbad
  let K := H.deleteEdges (starBadSupport G H J s P L t : Set (Sym2 W))
  let fH : (componentModel G t).Copy H := (SimpleGraph.Copy.ofLE K H (H.deleteEdges_le _)).comp f
  have hedge : (componentModel G t).edgeSet.Nonempty :=
    (Set.ncard_pos (s := (componentModel G t).edgeSet)).mp hsize
  obtain ⟨a, ha⟩ := hedge
  let a' : (componentModel G t).edgeSet := ⟨a, ha⟩
  let e : Sym2 W := (f.mapEdgeSet a').val
  have heK : e ∈ K.edgeSet := (f.mapEdgeSet a').property
  have heH : e ∈ H.edgeSet := by
    rw [H.edgeSet_deleteEdges] at heK
    exact heK.1
  have hecopy : e ∈ copyRawEdges fH := by
    apply (mem_copyRawEdges_iff_exists fH e).mpr
    exact ⟨a', rfl⟩
  have heBad : e ∈ starBadSupport G H J s P L t := by
    apply Finset.mem_filter.mpr
    exact ⟨SimpleGraph.mem_edgeFinset.mpr heH, fH, hecopy, hbad⟩
  rw [H.edgeSet_deleteEdges] at heK
  exact heK.2 heBad

theorem exists_star_pruned_type {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s k a D P : ℕ) (L η E : ℝ) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k a).Nonempty)
    (hbudget : H.edgeFinset.card * starBadTypeBound s k a D P L ≤
      η * E * (componentClass G k a).card) :
    ∃ t ∈ componentClass G k a, ((starBadSupport G H J s P L t).card : ℝ) ≤ η * E ∧
      ∀ f : (componentModel G t).Copy
          (H.deleteEdges (starBadSupport G H J s P L t : Set (Sym2 W))),
        ¬IsStarDeficitImage H J
          (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
          (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) s P L := by
  classical
  obtain ⟨t, ht, hsmall⟩ := exists_star_type_small_support G H J s k a D P L ha hP hD hlocal hclass
  have hpositive : (0 : ℝ) < (componentClass G k a).card := by exact_mod_cast hclass.card_pos
  have hcost : ((starBadSupport G H J s P L t).card : ℝ) ≤ η * E := by
    nlinarith only [hsmall.trans hbudget, hpositive]
  have hsize : 0 < componentSize G t := by
    have ht' := (Finset.mem_filter.mp ht).2.2
    omega
  exact ⟨t, ht, hcost, starBadSupport_eliminates_bad_copies G H J s P L t hsize⟩

end Erdos911
