import Erdos911.StarTypePruning

namespace Erdos911

noncomputable def imagePatternBadSupport {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (Q : Finset W → Finset (Finset (Sym2 W))) (t : ComponentType G) : Finset (Sym2 W) := by
  classical
  exact H.edgeFinset.filter (fun e => ∃ f : (componentModel G t).Copy H,
    e ∈ copyRawEdges f ∧ copyRawEdges f ∈ Q (copyVertices f))

theorem imagePatternBadSupport_subset {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (Q : Finset W → Finset (Finset (Sym2 W))) (t : ComponentType G) :
    imagePatternBadSupport G H Q t ⊆ H.edgeFinset := by
  classical
  exact Finset.filter_subset _ _

/-- An arbitrary finite family of image patterns can be counted over
component types by recording a rooted support and its edge subset. -/
theorem imagePatternBadSupport_incidence_bound {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (Q : Finset W → Finset (Finset (Sym2 W))) (k m D : ℕ) (B : ℝ)
    (hD : ∀ w, H.degree w ≤ D) (hB : 0 ≤ B)
    (hpatterns : ∀ U : Finset W, U.card = k → U.Nonempty → ((Q U).card : ℝ) ≤ B)
    (e : Sym2 W) :
    (((componentClass G k m).filter (fun t => e ∈ imagePatternBadSupport G H Q t)).card : ℝ) ≤
      (D ^ (2 * (k - 1)) : ℝ) * B := by
  classical
  let A := (componentClass G k m).filter (fun t => e ∈ imagePatternBadSupport G H Q t)
  let C := rootedConnectedSets H e.out.1 k
  have hdata (t : A) : componentOrder G t.val = k ∧ componentSize G t.val = m ∧
      ∃ f : (componentModel G t.val).Copy H, e ∈ copyRawEdges f ∧ copyRawEdges f ∈ Q (copyVertices f) := by
    obtain ⟨htclass, htsupport⟩ := Finset.mem_filter.mp t.property
    obtain ⟨hk, hm⟩ := (Finset.mem_filter.mp htclass).2
    exact ⟨hk, hm, (Finset.mem_filter.mp htsupport).2⟩
  choose f hef hpattern using fun t : A => (hdata t).2.2
  have hvertices (t : A) : copyVertices (f t) ∈ C := by
    have he := (mem_copyRawEdges_iff (f t) e).mp (hef t)
    have hroot := SimpleGraph.Subgraph.mem_verts_of_mem_edge he (Sym2.out_fst_mem e)
    rw [← copyVertices_eq_subgraph_verts (f t)] at hroot
    have hk : Fintype.card (componentRepresentative G t.val).supp = k := by
      simpa only [componentOrder, Nat.card_eq_fintype_card] using (hdata t).1
    simpa only [hk] using
      copyVertices_mem_rooted (f t) (componentModel_connected G t.val) e.out.1 hroot
  let encode : A → (Σ U : C, Q U.val) := fun t =>
    ⟨⟨copyVertices (f t), hvertices t⟩, ⟨copyRawEdges (f t), hpattern t⟩⟩
  have hinj : Function.Injective encode := by
    intro u v huv
    have hverts := congrArg (fun x : Σ U : C, Q U.val => x.1.val) huv
    have hedges := congrArg (fun x : Σ U : C, Q U.val => x.2.val) huv
    apply Subtype.ext
    exact (componentModel_iso_iff G u.val v.val).mp (iso_of_copy_images (f u) (f v) hverts hedges)
  have hcount : A.card ≤ ∑ U : C, (Q U.val).card := by
    have h := Fintype.card_le_of_injective encode hinj
    simpa only [Fintype.card_coe, Fintype.card_sigma] using h
  have hlocal (U : C) : ((Q U.val).card : ℝ) ≤ B := by
    have hU := (Finset.mem_filter.mp U.property).2
    exact hpatterns U.val hU.2.1 ⟨e.out.1, hU.1⟩
  have hC : (C.card : ℝ) ≤ (D ^ (2 * (k - 1)) : ℝ) := by
    exact_mod_cast rooted_connected_set_count H D hD e.out.1 k
  calc
    (A.card : ℝ) ≤ ∑ U : C, ((Q U.val).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _U : C, B := Finset.sum_le_sum (fun U _ => hlocal U)
    _ = C.card * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hB

theorem exists_imagePattern_type_small_support {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (Q : Finset W → Finset (Finset (Sym2 W))) (k m D : ℕ) (B : ℝ)
    (hD : ∀ w, H.degree w ≤ D) (hB : 0 ≤ B)
    (hpatterns : ∀ U : Finset W, U.card = k → U.Nonempty → ((Q U).card : ℝ) ≤ B)
    (hclass : (componentClass G k m).Nonempty) :
    ∃ t ∈ componentClass G k m,
      ((imagePatternBadSupport G H Q t).card : ℝ) * (componentClass G k m).card ≤
        H.edgeFinset.card * ((D ^ (2 * (k - 1)) : ℝ) * B) := by
  classical
  obtain ⟨t, ht, hsmall⟩ := exists_small_incidence_fiber_real (componentClass G k m) H.edgeFinset
    (fun t e => e ∈ imagePatternBadSupport G H Q t) hclass ((D ^ (2 * (k - 1)) : ℝ) * B)
    (fun e _ => imagePatternBadSupport_incidence_bound G H Q k m D B hD hB hpatterns e)
  have hfilter : H.edgeFinset.filter (fun e => e ∈ imagePatternBadSupport G H Q t) =
      imagePatternBadSupport G H Q t := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨imagePatternBadSupport_subset G H Q t h, h⟩⟩
  rw [hfilter] at hsmall
  exact ⟨t, ht, hsmall⟩

theorem imagePatternBadSupport_eliminates_bad_copies {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (Q : Finset W → Finset (Finset (Sym2 W))) (t : ComponentType G)
    (hsize : 0 < componentSize G t) :
    ∀ f : (componentModel G t).Copy
        (H.deleteEdges (imagePatternBadSupport G H Q t : Set (Sym2 W))),
      copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) ∉
        Q (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) := by
  classical
  intro f hbad
  let J := H.deleteEdges (imagePatternBadSupport G H Q t : Set (Sym2 W))
  let fH : (componentModel G t).Copy H := (SimpleGraph.Copy.ofLE J H (H.deleteEdges_le _)).comp f
  have hedge : (componentModel G t).edgeSet.Nonempty :=
    (Set.ncard_pos (s := (componentModel G t).edgeSet)).mp hsize
  obtain ⟨a, ha⟩ := hedge
  let a' : (componentModel G t).edgeSet := ⟨a, ha⟩
  let e : Sym2 W := (f.mapEdgeSet a').val
  have heJ : e ∈ J.edgeSet := (f.mapEdgeSet a').property
  have heH : e ∈ H.edgeSet := by
    rw [H.edgeSet_deleteEdges] at heJ
    exact heJ.1
  have hecopy : e ∈ copyRawEdges fH := (mem_copyRawEdges_iff_exists fH e).mpr ⟨a', rfl⟩
  have heBad : e ∈ imagePatternBadSupport G H Q t :=
    Finset.mem_filter.mpr ⟨H.mem_edgeFinset.mpr heH, fH, hecopy, hbad⟩
  rw [H.edgeSet_deleteEdges] at heJ
  exact heJ.2 heBad

end Erdos911
