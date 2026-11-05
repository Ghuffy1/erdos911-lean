import Erdos911.PatternFiberCounts
import Erdos911.IncidenceGraph

namespace Erdos911

def centerRows {L R : Type*} [DecidableEq L]
    (U : Finset R) (f : R → L) (x : L) : Finset R := U.filter (fun y => f y = x)

def centerNeighborhood {L R : Type*} [DecidableEq L]
    {U : Finset R} {f : R → L}
    (N : R → Finset L) (X : L → Finset L) (x : L) (y : ↥(centerRows U f x)) : Finset ↥(X x) :=
  (N y.val).subtype (fun z => z ∈ X x)

theorem centerNeighborhood_card {L R : Type*} [DecidableEq L]
    (N : R → Finset L) (U : Finset R) (f : R → L) (X : L → Finset L)
    (hsub : ∀ y ∈ U, N y ⊆ X (f y)) (x : L) (y : ↥(centerRows U f x)) :
    (centerNeighborhood (U := U) (f := f) N X x y).card = (N y.val).card := by
  obtain ⟨hy, hfx⟩ := Finset.mem_filter.mp y.property
  have hs : N y.val ⊆ X x := by simpa only [hfx] using hsub y.val hy
  rw [centerNeighborhood, Finset.card_subtype, Finset.filter_eq_self.mpr hs]

def centerVertexMap {L R : Type*} [DecidableEq L]
    (U : Finset R) (f : R → L) (X : L → Finset L) (x : L) :
    ↥(X x) ⊕ ↥(centerRows U f x) → L ⊕ R
  | Sum.inl z => Sum.inl z.val
  | Sum.inr y => Sum.inr y.val

theorem centerVertexMap_injective {L R : Type*} [DecidableEq L]
    (U : Finset R) (f : R → L) (X : L → Finset L) (x : L) :
    Function.Injective (centerVertexMap U f X x) := by
  intro a b h
  cases a <;> cases b
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (Subtype.ext (Sum.inr_injective h))

def centerBlockCopy {L R : Type*} [DecidableEq L]
    (N : R → Finset L) (U : Finset R) (f : R → L) (X : L → Finset L) (x : L) :
    (incidenceGraph (centerNeighborhood (U := U) (f := f) N X x)).Copy (incidenceGraph N) where
  toHom := {
    toFun := centerVertexMap U f X x
    map_rel' := by
      intro a b h
      cases a <;> cases b
      · exact h.elim
      · exact Finset.mem_subtype.mp h
      · exact Finset.mem_subtype.mp h
      · exact h.elim }
  injective' := centerVertexMap_injective U f X x

theorem centerRows_sum {L R : Type*} [DecidableEq L]
    (U : Finset R) (f : R → L) :
    (∑ x : ↥(U.image f), Fintype.card ↥(centerRows U f x.val)) = U.card := by
  classical
  simp only [Fintype.card_coe]
  calc
    (∑ x : ↥(U.image f), (centerRows U f x.val).card) =
        ∑ x ∈ U.image f, (centerRows U f x).card :=
      Finset.sum_coe_sort (U.image f) (fun x => (centerRows U f x).card)
    _ = U.card := sum_pattern_fiber_cards U f (U.image f) (fun y hy => Finset.mem_image_of_mem f hy)

/-- Distinct center blocks have disjoint vertex domains on both sides. -/
theorem centerVertexMap_sigma_injective {L R : Type*} [DecidableEq L]
    (U : Finset R) (f : R → L) (X : L → Finset L)
    (hdisj : ∀ x ∈ U.image f, ∀ z ∈ U.image f, x ≠ z → Disjoint (X x) (X z)) :
    Function.Injective (fun v : (Σ x : ↥(U.image f), ↥(X x.val) ⊕ ↥(centerRows U f x.val)) =>
      centerVertexMap U f X v.1.val v.2) := by
  classical
  rintro ⟨x, a⟩ ⟨z, b⟩ h
  have hxz : x = z := by
    apply Subtype.ext
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        by_contra hne
        have heq : a.val = b.val := Sum.inl_injective h
        exact Finset.disjoint_left.mp (hdisj x.val x.property z.val z.property hne)
          a.property (heq.symm ▸ b.property)
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b =>
        have heq : a.val = b.val := Sum.inr_injective h
        have ha := (Finset.mem_filter.mp a.property).2
        have hb := (Finset.mem_filter.mp b.property).2
        exact ha.symm.trans ((congrArg f heq).trans hb)
  subst z
  have hab := centerVertexMap_injective U f X x.val h
  cases hab
  rfl

end Erdos911
