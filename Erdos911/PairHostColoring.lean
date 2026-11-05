import Erdos911.RedIncidencePairObstruction
import Erdos911.BipartiteRestriction

namespace Erdos911

noncomputable def restrictedHostRows {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (y : ↥B) : Finset V := by
  classical
  exact A.filter (fun x => K.Adj x y.val)

theorem mem_restrictedHostRows {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (y : ↥B) (x : V) :
    x ∈ restrictedHostRows K A B y ↔ x ∈ A ∧ K.Adj x y.val := by
  classical
  exact Finset.mem_filter

theorem restrictedHostRows_row_bound {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (A B : Finset V) (y : ↥B) :
    (restrictedHostRows K A B y).card ≤ K.degree y.val := by
  classical
  rw [← K.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  exact (K.mem_neighborFinset y.val x).mpr ((mem_restrictedHostRows K A B y x).mp hx).2.symm

theorem restrictedHostRows_column_bound {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (A B : Finset V) (D : ℕ)
    (hA : ∀ x ∈ A, K.degree x ≤ D) (x : V) :
    (incidenceColumn (restrictedHostRows K A B) x).card ≤ D := by
  classical
  by_cases hx : x ∈ A
  · have hsub : (incidenceColumn (restrictedHostRows K A B) x).image Subtype.val ⊆ K.neighborFinset x := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hm := (Finset.mem_filter.mp hz).2
      exact (K.mem_neighborFinset x z.val).mpr ((mem_restrictedHostRows K A B z x).mp hm).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective, K.card_neighborFinset_eq_degree] at hc
    exact hc.trans (hA x hx)
  · have hz : incidenceColumn (restrictedHostRows K A B) x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hx ((mem_restrictedHostRows K A B y x).mp (Finset.mem_filter.mp hy).2).1
    rw [hz, Finset.card_empty]
    exact Nat.zero_le _

noncomputable def pairHostRed {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (ω : Sym2 V → Bool) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((∃ hv : v ∈ B, u ∈ pairRedRow (restrictedHostRows K A B ⟨v, hv⟩) ω) ∨
    (∃ hu : u ∈ B, v ∈ pairRedRow (restrictedHostRows K A B ⟨u, hu⟩) ω))
  symm.symm _u _v h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _u h := h.1 rfl

theorem pairHostRed_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (ω : Sym2 V → Bool) : pairHostRed K A B ω ≤ K := by
  intro u v h
  rcases h.2 with ⟨hv, hu⟩ | ⟨hu, hv⟩
  · exact ((mem_restrictedHostRows K A B ⟨v, hv⟩ u).mp (Finset.mem_sdiff.mp hu).1).2
  · exact ((mem_restrictedHostRows K A B ⟨u, hu⟩ v).mp (Finset.mem_sdiff.mp hv).1).2.symm

theorem pairHostRed_bipartite {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (ω : Sym2 V → Bool) (hAB : Disjoint A B) :
    (pairHostRed K A B ω).IsBipartiteWith (A : Set V) (B : Set V) := by
  constructor
  · exact_mod_cast hAB
  · intro u v h
    rcases h.2 with ⟨hv, hu⟩ | ⟨hu, hv⟩
    · exact Or.inl ⟨((mem_restrictedHostRows K A B ⟨v, hv⟩ u).mp (Finset.mem_sdiff.mp hu).1).1, hv⟩
    · exact Or.inr ⟨hu, ((mem_restrictedHostRows K A B ⟨u, hu⟩ v).mp (Finset.mem_sdiff.mp hv).1).1⟩

theorem pairHostRed_between_iff {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (ω : Sym2 V → Bool) (hAB : Disjoint A B)
    (u v : V) (hu : u ∈ A) (hv : v ∈ B) :
    (pairHostRed K A B ω).Adj u v ↔ u ∈ pairRedRow (restrictedHostRows K A B ⟨v, hv⟩) ω := by
  constructor
  · intro h
    rcases h.2 with ⟨hv', hred⟩ | ⟨huB, _⟩
    · exact hred
    · exact (Finset.disjoint_left.mp hAB hu huB).elim
  · intro h
    refine ⟨?_, Or.inl ⟨hv, h⟩⟩
    intro heq
    exact Finset.disjoint_left.mp hAB hu (heq.symm ▸ hv)

theorem pairHostBlue_between {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A B : Finset V) (ω : Sym2 V → Bool) (hAB : Disjoint A B)
    (u v : V) (hu : u ∈ A) (hv : v ∈ B)
    (hblue : (K \ pairHostRed K A B ω).Adj u v) :
    u ∈ pairBlueRow (restrictedHostRows K A B ⟨v, hv⟩) ω := by
  have hN : u ∈ restrictedHostRows K A B ⟨v, hv⟩ := (mem_restrictedHostRows K A B ⟨v, hv⟩ u).mpr ⟨hu, hblue.1⟩
  by_contra hnot
  have hred : u ∈ pairRedRow (restrictedHostRows K A B ⟨v, hv⟩) ω := Finset.mem_sdiff.mpr ⟨hN, hnot⟩
  exact hblue.2 ((pairHostRed_between_iff K A B ω hAB u v hu hv).mpr hred)

end Erdos911
