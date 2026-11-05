import Erdos911.OrientationPatterns
import Erdos911.ComponentModels
import Erdos911.StarTypePruning

namespace Erdos911

noncomputable def IsOrientationBadType {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (root : W) (T k a e : ℕ) (g : ℝ) (t : ComponentType G) : Prop :=
  componentOrder G t = k ∧ componentSize G t = e ∧
    ∃ f : (componentModel G t).Copy H, root ∈ copyVertices f ∧
      copyRawEdges f ∈ orientationPatterns H K T (copyVertices f) a e g

noncomputable def orientationBadTypes {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (root : W) (T k a e : ℕ) (g : ℝ) : Finset (ComponentType G) := by
  classical
  exact Finset.univ.filter (IsOrientationBadType G H K root T k a e g)

noncomputable def orientationBadTypeBound (T k a e D : ℕ) (g : ℝ) : ℝ :=
  (D ^ (2 * (k - 1)) : ℝ) * (2 : ℝ) ^ k * (e + 1 : ℝ) *
    Real.exp ((e : ℝ) * Real.log ((T * k : ℝ) / e) - g * Real.log ((k : ℝ) / a) + 2 * e)

/-- The count is over component types, rather than labelled embeddings.
Both their image support and their edge subset are recorded. -/
theorem orientationBadTypes_card_bound {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (root : W) (T k a e D : ℕ) (g : ℝ)
    (hT : 0 < T) (ha : 0 < a) (he : 0 < e) (hak : a ≤ k)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ T * k) :
    ((orientationBadTypes G H K root T k a e g).card : ℝ) ≤ orientationBadTypeBound T k a e D g := by
  classical
  let B := orientationBadTypes G H K root T k a e g
  let C := rootedConnectedSets H root k
  let patterns := fun U : C => orientationPatterns H K T U.val a e g
  let b : ℝ := (2 : ℝ) ^ k * (e + 1 : ℝ) *
    Real.exp ((e : ℝ) * Real.log ((T * k : ℝ) / e) - g * Real.log ((k : ℝ) / a) + 2 * e)
  have hdata : ∀ t : B, IsOrientationBadType G H K root T k a e g t.val := by
    intro t
    exact (Finset.mem_filter.mp t.property).2
  have hex : ∀ t : B, ∃ f : (componentModel G t.val).Copy H, root ∈ copyVertices f ∧
      copyRawEdges f ∈ orientationPatterns H K T (copyVertices f) a e g := fun t => (hdata t).2.2
  choose f hfroot hfbad using hex
  have horder : ∀ t : B, Fintype.card (componentRepresentative G t.val).supp = k := by
    intro t
    simpa only [componentOrder, Nat.card_eq_fintype_card] using (hdata t).1
  have hvertices : ∀ t : B, copyVertices (f t) ∈ C := by
    intro t
    have h := copyVertices_mem_rooted (f t) (componentModel_connected G t.val) root (hfroot t)
    simpa only [horder t] using h
  have hpatterns : ∀ t : B, copyRawEdges (f t) ∈ patterns ⟨copyVertices (f t), hvertices t⟩ := hfbad
  let encode : B → (Σ U : C, patterns U) := fun t =>
    ⟨⟨copyVertices (f t), hvertices t⟩, ⟨copyRawEdges (f t), hpatterns t⟩⟩
  have hinj : Function.Injective encode := by
    intro u v huv
    have hverts := congrArg (fun x : Σ U : C, patterns U => x.1.val) huv
    have hedges := congrArg (fun x : Σ U : C, patterns U => x.2.val) huv
    apply Subtype.ext
    exact (componentModel_iso_iff G u.val v.val).mp (iso_of_copy_images (f u) (f v) hverts hedges)
  have hpatternBound : ∀ U : C, ((patterns U).card : ℝ) ≤ b := by
    intro U
    have hUk : U.val.card = k := (Finset.mem_filter.mp U.property).2.2.1
    simpa only [patterns, b, hUk] using orientationPatterns_card_bound H K hHK T U.val a e g
      hT ha he (by simpa only [hUk] using hak) (by simpa only [hUk] using hlocal U.val hUk)
  have hcount : B.card ≤ ∑ U : C, (patterns U).card := by
    have h := Fintype.card_le_of_injective encode hinj
    simpa only [Fintype.card_coe, Fintype.card_sigma] using h
  have hC : (C.card : ℝ) ≤ (D ^ (2 * (k - 1)) : ℝ) := by
    exact_mod_cast rooted_connected_set_count H D hD root k
  calc
    (B.card : ℝ) ≤ ∑ U : C, ((patterns U).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _U : C, b := Finset.sum_le_sum (fun U _ => hpatternBound U)
    _ = (C.card : ℝ) * b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (D ^ (2 * (k - 1)) : ℝ) * b := mul_le_mul_of_nonneg_right hC (by dsimp only [b]; positivity)
    _ = _ := by dsimp only [b, orientationBadTypeBound]; ring

noncomputable def orientationBadSupport {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T a : ℕ) (g : ℝ) (t : ComponentType G) : Finset (Sym2 W) := by
  classical
  exact H.edgeFinset.filter (fun e => ∃ f : (componentModel G t).Copy H,
    e ∈ copyRawEdges f ∧ copyRawEdges f ∈
      orientationPatterns H K T (copyVertices f) a (componentSize G t) g)

theorem orientationBadSupport_subset {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T a : ℕ) (g : ℝ) (t : ComponentType G) : orientationBadSupport G H K T a g t ⊆ H.edgeFinset := by
  classical
  exact Finset.filter_subset _ _

theorem orientationBadSupport_incidence_subset {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T k a m : ℕ) (g : ℝ) (e : Sym2 W) :
    ((componentClass G k m).filter (fun t => e ∈ orientationBadSupport G H K T a g t)) ⊆
      orientationBadTypes G H K e.out.1 T k a m g := by
  classical
  intro t ht
  obtain ⟨htclass, htsupport⟩ := Finset.mem_filter.mp ht
  obtain ⟨hk, hm⟩ := (Finset.mem_filter.mp htclass).2
  obtain ⟨f, hef, hbad⟩ := (Finset.mem_filter.mp htsupport).2
  have hroot : e.out.1 ∈ copyVertices f := by
    have he := (mem_copyRawEdges_iff f e).mp hef
    have hv := SimpleGraph.Subgraph.mem_verts_of_mem_edge he (Sym2.out_fst_mem e)
    rw [← copyVertices_eq_subgraph_verts f] at hv
    exact hv
  rw [hm] at hbad
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hm, f, hroot, hbad⟩

theorem exists_orientation_type_small_support {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (T k a e D : ℕ) (g : ℝ)
    (hT : 0 < T) (ha : 0 < a) (he : 0 < e) (hak : a ≤ k)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ T * k)
    (hclass : (componentClass G k e).Nonempty) :
    ∃ t ∈ componentClass G k e,
      ((orientationBadSupport G H K T a g t).card : ℝ) * (componentClass G k e).card ≤
        H.edgeFinset.card * orientationBadTypeBound T k a e D g := by
  classical
  have hincidence : ∀ b ∈ H.edgeFinset,
      (((componentClass G k e).filter (fun t => b ∈ orientationBadSupport G H K T a g t)).card : ℝ) ≤
        orientationBadTypeBound T k a e D g := by
    intro b _
    have hsubset := Finset.card_le_card (orientationBadSupport_incidence_subset G H K T k a e g b)
    have hreal : (((componentClass G k e).filter
        (fun t => b ∈ orientationBadSupport G H K T a g t)).card : ℝ) ≤
        (orientationBadTypes G H K b.out.1 T k a e g).card := by exact_mod_cast hsubset
    exact hreal.trans (orientationBadTypes_card_bound G H K hHK b.out.1 T k a e D g
      hT ha he hak hD hlocal)
  obtain ⟨t, ht, hsmall⟩ := exists_small_incidence_fiber_real (componentClass G k e) H.edgeFinset
    (fun t b => b ∈ orientationBadSupport G H K T a g t) hclass
    (orientationBadTypeBound T k a e D g) hincidence
  have hfilter : H.edgeFinset.filter (fun b => b ∈ orientationBadSupport G H K T a g t) =
      orientationBadSupport G H K T a g t := by
    ext b
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨orientationBadSupport_subset G H K T a g t h, h⟩⟩
  rw [hfilter] at hsmall
  exact ⟨t, ht, hsmall⟩

theorem orientationBadSupport_eliminates_bad_copies {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T a : ℕ) (g : ℝ) (t : ComponentType G) (hsize : 0 < componentSize G t) :
    ∀ f : (componentModel G t).Copy
        (H.deleteEdges (orientationBadSupport G H K T a g t : Set (Sym2 W))),
      copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) ∉
        orientationPatterns H K T
          (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) a (componentSize G t) g := by
  classical
  intro f hbad
  let J := H.deleteEdges (orientationBadSupport G H K T a g t : Set (Sym2 W))
  let fH : (componentModel G t).Copy H := (SimpleGraph.Copy.ofLE J H (H.deleteEdges_le _)).comp f
  have hedge : (componentModel G t).edgeSet.Nonempty :=
    (Set.ncard_pos (s := (componentModel G t).edgeSet)).mp hsize
  obtain ⟨b, hb⟩ := hedge
  let b' : (componentModel G t).edgeSet := ⟨b, hb⟩
  let e : Sym2 W := (f.mapEdgeSet b').val
  have heJ : e ∈ J.edgeSet := (f.mapEdgeSet b').property
  have heH : e ∈ H.edgeSet := by
    rw [H.edgeSet_deleteEdges] at heJ
    exact heJ.1
  have hecopy : e ∈ copyRawEdges fH :=
    (mem_copyRawEdges_iff_exists fH e).mpr ⟨b', rfl⟩
  have heBad : e ∈ orientationBadSupport G H K T a g t :=
    Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr heH, fH, hecopy, hbad⟩
  rw [H.edgeSet_deleteEdges] at heJ
  exact heJ.2 heBad

end Erdos911
