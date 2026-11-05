import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

namespace Erdos911

def pairEndpoints {E : Type*} [DecidableEq E] (p : E × E) : Finset E := {p.1, p.2}

def IsPairPacking {E : Type*} [DecidableEq E] (S : Finset E) (P : Finset (E × E)) : Prop :=
  (∀ p ∈ P, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 ≠ p.2) ∧
    (P : Set (E × E)).PairwiseDisjoint pairEndpoints

theorem IsPairPacking.endpoints_subset {E : Type*} [DecidableEq E]
    {S : Finset E} {P : Finset (E × E)} (hP : IsPairPacking S P) {p : E × E} (hp : p ∈ P) :
    pairEndpoints p ⊆ S := by
  intro x hx
  simp only [pairEndpoints, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (hP.1 p hp).1
  · exact (hP.1 p hp).2.1

theorem IsPairPacking.mono {E : Type*} [DecidableEq E]
    {S : Finset E} {P Q : Finset (E × E)} (hP : IsPairPacking S P) (hQP : Q ⊆ P) :
    IsPairPacking S Q :=
  ⟨fun p hp => hP.1 p (hQP hp), fun _ hp _ hq hpq => hP.2 (hQP hp) (hQP hq) hpq⟩

def pairVertexUnion {E : Type*} [DecidableEq E] (P : Finset (E × E)) : Finset E :=
  P.biUnion pairEndpoints

theorem IsPairPacking.union_subset {E : Type*} [DecidableEq E]
    {S : Finset E} {P : Finset (E × E)} (hP : IsPairPacking S P) : pairVertexUnion P ⊆ S := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
  exact hP.endpoints_subset hp hxp

theorem IsPairPacking.union_card {E : Type*} [DecidableEq E]
    {S : Finset E} {P : Finset (E × E)} (hP : IsPairPacking S P) :
    (pairVertexUnion P).card = 2 * P.card := by
  rw [pairVertexUnion, Finset.card_biUnion hP.2]
  calc
    (∑ p ∈ P, (pairEndpoints p).card) = ∑ _p ∈ P, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [pairEndpoints, (hP.1 p hp).2.2]
    _ = 2 * P.card := by simp [mul_comm]

/-- Every finite set contains a collection of disjoint two-element pairs
of cardinality equal to half its order rounded down. -/
theorem exists_pair_packing {E : Type*} [DecidableEq E] (S : Finset E) :
    ∃ P : Finset (E × E), IsPairPacking S P ∧ P.card = S.card / 2 := by
  classical
  let label : Fin S.card ≃ S := (Finset.equivFin S).symm
  let endpoint : Fin (S.card / 2) × Fin 2 → E := fun p =>
    (label ⟨2 * p.1.val + p.2.val, by
      have hi := p.1.isLt
      have hj := p.2.isLt
      omega⟩).val
  have hendpoint_mem : ∀ p, endpoint p ∈ S := by
    intro p
    exact (label ⟨2 * p.1.val + p.2.val, by
      have hi := p.1.isLt
      have hj := p.2.isLt
      omega⟩).property
  have hendpoint : Function.Injective endpoint := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hindex := congrArg Fin.val (label.injective (Subtype.ext h))
    change 2 * i.val + a.val = 2 * j.val + b.val at hindex
    have ha : a.val < 2 := a.isLt
    have hb : b.val < 2 := b.isLt
    have hi : i.val = j.val := by omega
    have hab : a.val = b.val := by omega
    exact Prod.ext (Fin.ext hi) (Fin.ext hab)
  let pair : Fin (S.card / 2) → E × E := fun i => (endpoint (i, 0), endpoint (i, 1))
  have hpair : Function.Injective pair := by
    intro i j h
    exact congrArg Prod.fst (hendpoint (congrArg Prod.fst h))
  let P : Finset (E × E) := Finset.univ.image pair
  have hside : ∀ i x, x ∈ pairEndpoints (pair i) →
      ∃ a : Fin 2, endpoint (i, a) = x := by
    intro i x hx
    change x ∈ {endpoint (i, 0), endpoint (i, 1)} at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩
  refine ⟨P, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨hendpoint_mem (i, 0), hendpoint_mem (i, 1), ?_⟩
    intro h
    have hbad := congrArg (fun p : Fin (S.card / 2) × Fin 2 => p.2.val) (hendpoint h)
    norm_num at hbad
  · intro p hp q hq hpq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨a, ha⟩ := hside i x hxi
    obtain ⟨b, hb⟩ := hside j x hxj
    have hij : i = j := congrArg Prod.fst (hendpoint (ha.trans hb.symm))
    exact hpq (congrArg pair hij)
  · change (Finset.univ.image pair).card = S.card / 2
    rw [Finset.card_image_of_injective _ hpair, Finset.card_univ, Fintype.card_fin]

end Erdos911
