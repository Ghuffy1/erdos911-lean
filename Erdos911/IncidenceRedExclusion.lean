import Erdos911.IncidenceCapacity
import Erdos911.SeedMatchingObstruction

namespace Erdos911

theorem copy_vertex_unmarked_of_cross_neighbor {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H : SimpleGraph W) (f : F.Copy H) (S high : Finset W)
    (havoid : Disjoint (copyRawEdges f) (rectangleEdges H S high))
    (v : V) (hhigh : ∃ u, F.Adj v u ∧ f u ∈ high) : f v ∉ S := by
  intro hv
  obtain ⟨u, huv, hu⟩ := hhigh
  have hcopy : s(f v, f u) ∈ copyRawEdges f :=
    (mem_copyRawEdges_iff_exists f _).mpr ⟨⟨s(v, u), huv⟩, rfl⟩
  have hmark : s(f v, f u) ∈ rectangleEdges H S high :=
    (mem_rectangleEdges H S high _).mpr ⟨f v, hv, f u, hu, map_rel f.toHom huv, rfl⟩
  exact Finset.disjoint_left.mp havoid hcopy hmark

theorem cross_blocked_role_exceptional {V W I : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (H : SimpleGraph W) (f : F.Copy H) (high : Finset W)
    (L : V → Finset W) (B : I → Finset W) (h : ℕ) (marks : (Fin h × I) → Bool)
    (havoid : Disjoint (copyRawEdges f) (rectangleEdges H (roundMarkedVertices B h marks) high))
    (E : Finset V) (htrue : ∀ v, (L v).Nonempty → v ∉ E → f v ∈ L v)
    (hhigh : ∀ v, (L v).Nonempty → v ∉ E → ∃ u, F.Adj v u ∧ f u ∈ high)
    (v : V) (hne : (L v).Nonempty) (hv : marks ∈ listBlocked B h (L v)) : v ∈ E := by
  classical
  by_contra hn
  have hmarked := (listBlocked_iff_subset_roundMarked B h (L v) marks).mp hv (htrue v hne hn)
  exact copy_vertex_unmarked_of_cross_neighbor F H f _ high havoid v (hhigh v hne hn) hmarked

theorem cross_copy_few_blocked {V W I K : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [Fintype I] [Fintype K]
    (F : SimpleGraph V) (H : SimpleGraph W) (f : F.Copy H) (high : Finset W)
    (L : V → Finset W) (B : I → Finset W) (h : ℕ) (marks : (Fin h × I) → Bool)
    (havoid : Disjoint (copyRawEdges f) (rectangleEdges H (roundMarkedVertices B h marks) high))
    (E : Finset V) (htrue : ∀ v, (L v).Nonempty → v ∉ E → f v ∈ L v)
    (hhigh : ∀ v, (L v).Nonempty → v ∉ E → ∃ u, F.Adj v u ∧ f u ∈ high)
    (role : K → V) (hrole : Function.Injective role) (hne : ∀ k, (L (role k)).Nonempty) :
    (∑ k, (listBlocked B h (L (role k))).indicator (fun _ => (1 : ℝ)) marks) ≤ E.card := by
  classical
  let A := Finset.univ.filter (fun k => marks ∈ listBlocked B h (L (role k)))
  have hsub : A.image role ⊆ E := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact cross_blocked_role_exceptional F H f high L B h marks havoid E htrue hhigh (role k)
      (hne k) (Finset.mem_filter.mp hk).2
  have hcard : A.card ≤ E.card := by
    rw [← Finset.card_image_of_injective A hrole]
    exact Finset.card_le_card hsub
  have hsum : (∑ k, (listBlocked B h (L (role k))).indicator (fun _ => (1 : ℝ)) marks) = A.card := by
    simp only [Set.indicator, A, Finset.sum_boole]
  exact hsum.trans_le (by exact_mod_cast hcard)

theorem incidence_copy_thickMatchingEvent {V W I : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (H J : SimpleGraph W) (f : F.Copy H) (high : Finset W)
    (L : V → Finset W) (r : ℕ) (T u : ℝ) (B : I → Finset W) (h : ℕ)
    (marks : (Fin h × I) → Bool)
    (havoid : Disjoint (copyRawEdges f) (rectangleEdges H (roundMarkedVertices B h marks) high))
    (E : Finset V) (hE : (E.card : ℝ) ≤ u)
    (htrue : ∀ v, (L v).Nonempty → v ∉ E → f v ∈ L v)
    (hhigh : ∀ v, (L v).Nonempty → v ∉ E → ∃ w, F.Adj v w ∧ f w ∈ high) :
    marks ∈ thickMatchingEvent J L r T B h u := by
  classical
  let matching := maximumListMatching (fun v : thickCandidateRoles J L r T => L v.val)
  let role := fun k : matchedRoles matching => k.val.val
  have hrole : Function.Injective role := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hne (k : matchedRoles matching) : (L (role k)).Nonempty :=
    ((mem_thickCandidateRoles J L r T k.val.val).mp k.val.property).1
  exact (cross_copy_few_blocked F H f high L B h marks havoid E htrue hhigh role hrole hne).trans hE

/-- A cross-edge mark blocks a true candidate through one of its high
neighbors. Earlier edge deletions only restrict the copies needing a certificate. -/
theorem no_copy_of_cross_events_after_deletions {V W I A : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (H J : SimpleGraph W) (high : Finset W)
    (C : Finset A) (L : A → V → Finset W) (r : ℕ) (T u : ℝ)
    (P : Finset (Sym2 W)) (B : I → Finset W) (h : ℕ) (marks : (Fin h × I) → Bool)
    (hmarks : ∀ c : C, marks ∉ thickMatchingEvent J (L c.val) r T B h u)
    (hcertificate : ∀ f : F.Copy H, Disjoint (copyRawEdges f) P → ∃ c ∈ C, ∃ E : Finset V,
      (E.card : ℝ) ≤ u ∧ (∀ v, (L c v).Nonempty → v ∉ E → f v ∈ L c v) ∧
      ∀ v, (L c v).Nonempty → v ∉ E → ∃ w, F.Adj v w ∧ f w ∈ high) :
    ¬F.IsContained (H.deleteEdges
      ((P ∪ rectangleEdges H (roundMarkedVertices B h marks) high : Finset (Sym2 W)) : Set (Sym2 W))) := by
  classical
  rintro ⟨f⟩
  let fH := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
  have hdisjoint := copy_deleteEdges_disjoint F H
    (P ∪ rectangleEdges H (roundMarkedVertices B h marks) high) f
  obtain ⟨hprior, hcross⟩ := Finset.disjoint_union_right.mp hdisjoint
  obtain ⟨c, hc, E, hE, htrue, hhigh⟩ := hcertificate fH hprior
  exact hmarks ⟨c, hc⟩ (incidence_copy_thickMatchingEvent F H J fH high (L c) r T u B h marks
    hcross E hE htrue hhigh)

end Erdos911
