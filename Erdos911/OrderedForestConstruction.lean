import Erdos911.ComponentRoots
import Erdos911.OrderedForestSampling

namespace Erdos911

theorem ordered_parent_adj {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (e : Fin n → V) (parent : (i : Fin n) → Option (Fin i.val))
    (hedges : ∀ i k, parent i = some k → G.Adj (initialSegment e i k) (e i))
    (i j : Fin n) (hparent : orderedParent parent i = some j) : G.Adj (e j) (e i) := by
  cases hp : parent i with
  | none => simp [orderedParent, hp] at hparent
  | some k =>
    have heq : (⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ : Fin n) = j := by
      simpa only [orderedParent, hp, Option.map_some, Option.some.injEq] using hparent
    have h := hedges i k hp
    change G.Adj (e ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) (e i) at h
    rwa [heq] at h

theorem parentFiberCard_le_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (e : Fin n → V) (he : Function.Injective e)
    (parent : (i : Fin n) → Option (Fin i.val))
    (hedges : ∀ i k, parent i = some k → G.Adj (initialSegment e i k) (e i)) (j : Fin n) :
    parentFiberCard parent (some j) ≤ G.degree (e j) := by
  classical
  let A := Finset.univ.filter (fun i => orderedParent parent i = some j)
  have hsubset : A.image e ⊆ G.neighborFinset (e j) := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    apply (G.mem_neighborFinset (e j) (e i)).mpr
    exact ordered_parent_adj G e parent hedges i j (Finset.mem_filter.mp hi).2
  calc
    parentFiberCard parent (some j) = A.card := rfl
    _ = (A.image e).card := (Finset.card_image_of_injective A he).symm
    _ ≤ (G.neighborFinset (e j)).card := Finset.card_le_card hsubset
    _ = G.degree (e j) := G.card_neighborFinset_eq_degree _

/-- Order a finite graph by distance to its component roots, with a vertex
label as tie-breaker. Each nonroot receives an earlier adjacent parent. -/
theorem exists_ordered_spanning_forest {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (e : Fin (Fintype.card V) ≃ V)
      (parent : (i : Fin (Fintype.card V)) → Option (Fin i.val)),
      (∀ i k, parent i = some k → G.Adj (initialSegment (fun j => e j) i k) (e i)) ∧
        parentFiberCard parent none = Nat.card G.ConnectedComponent ∧
          ∀ j, parentFiberCard parent (some j) ≤ G.degree (e j) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_ordered_by_key (forestOrderKey G) (forestOrderKey_injective G)
  have hprior : ∀ i : Fin (Fintype.card V), e i ≠ componentRoot G (e i) →
      ∃ k : Fin i.val, G.Adj (initialSegment (fun j => e j) i k) (e i) := by
    intro i hi
    obtain ⟨v, hadj, hkey⟩ := exists_smaller_neighbor_key G (e i) hi
    have hindex : e.symm v < i := by
      apply (he (e.symm v) i).mp
      simpa only [e.apply_symm_apply] using hkey
    refine ⟨⟨(e.symm v).val, hindex⟩, ?_⟩
    change G.Adj (e ⟨(e.symm v).val, _⟩) (e i)
    have hsame : (⟨(e.symm v).val, Nat.lt_trans hindex i.isLt⟩ : Fin (Fintype.card V)) =
        e.symm v := Fin.ext rfl
    simpa only [hsame, e.apply_symm_apply] using hadj
  let parent : (i : Fin (Fintype.card V)) → Option (Fin i.val) := fun i =>
    if h : e i = componentRoot G (e i) then none else some (Classical.choose (hprior i h))
  have hedges : ∀ i k, parent i = some k →
      G.Adj (initialSegment (fun j => e j) i k) (e i) := by
    intro i k hk
    by_cases hroot : e i = componentRoot G (e i)
    · simp only [parent, dite_eq_left hroot, reduceCtorEq] at hk
    · have hsame : Classical.choose (hprior i hroot) = k := by
        simpa only [parent, dite_eq_right hroot, Option.some.injEq] using hk
      rw [← hsame]
      exact Classical.choose_spec (hprior i hroot)
  have hnone : ∀ i, orderedParent parent i = none ↔ componentRoot G (e i) = e i := by
    intro i
    by_cases hroot : e i = componentRoot G (e i)
    · constructor
      · intro _
        exact hroot.symm
      · intro _
        simp only [orderedParent, parent, dite_eq_left hroot, Option.map_none]
    · constructor
      · intro h
        have hfalse : False := by
          simp only [orderedParent, parent, dite_eq_right hroot, Option.map_some, reduceCtorEq] at h
        exact hfalse.elim
      · intro h
        exact (hroot h.symm).elim
  let A := Finset.univ.filter (fun i => orderedParent parent i = none)
  let B := Finset.univ.filter (fun v => componentRoot G v = v)
  have himage : A.image e = B := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hnone i).mp (Finset.mem_filter.mp hi).2⟩
    · intro hv
      have hvroot := (Finset.mem_filter.mp hv).2
      apply Finset.mem_image.mpr
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (hnone _).mpr ?_⟩
      simpa only [e.apply_symm_apply] using hvroot
  refine ⟨e, parent, hedges, ?_, ?_⟩
  · calc
      parentFiberCard parent none = A.card := rfl
      _ = (A.image e).card := (Finset.card_image_of_injective A e.injective).symm
      _ = B.card := congrArg Finset.card himage
      _ = Nat.card G.ConnectedComponent := component_roots_card G
  · exact parentFiberCard_le_degree G (fun j => e j) e.injective parent hedges

end Erdos911
