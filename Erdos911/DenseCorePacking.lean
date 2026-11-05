import Erdos911.InducedDegreeCore

namespace Erdos911

def DegreeCoreFamily {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (K s : ℕ) (P : Finset (Finset V)) : Prop :=
  (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
    ∀ T ∈ P, T.Nonempty ∧ T.card ≤ K ∧
      ∀ v : ↥(T : Set V), s ≤ ((G.induce (T : Set V)).neighborSet v).ncard

/-- A maximal disjoint packing of small induced degree cores leaves
every small set in its complement with at most s times its order edges. -/
theorem exists_dense_core_packing {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (K s : ℕ) :
    ∃ P : Finset (Finset V), DegreeCoreFamily G K s P ∧
      ∀ T : Finset V, Disjoint T (P.biUnion id) → T.card ≤ K →
        ((G.induce (T : Set V)).edgeSet.ncard : ℝ) ≤ (s : ℝ) * T.card := by
  classical
  let families := Finset.univ.filter (DegreeCoreFamily G K s)
  have hfamilies : families.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simp [DegreeCoreFamily]
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image families (fun P => (P.biUnion id).card) hfamilies
  have hgood : DegreeCoreFamily G K s P := (Finset.mem_filter.mp hP).2
  refine ⟨P, hgood, ?_⟩
  intro T hdisjoint hTK
  by_contra hnot
  obtain ⟨U, hUT, hUne, hUcore⟩ := exists_induced_degree_core G T s (lt_of_not_ge hnot)
  have hUdisjoint : Disjoint U (P.biUnion id) := Finset.disjoint_of_subset_left hUT hdisjoint
  have hUA (A : Finset V) (hA : A ∈ P) : Disjoint U A := by
    apply Finset.disjoint_of_subset_right _ hUdisjoint
    exact Finset.subset_biUnion_of_mem id hA
  have hUnot : U ∉ P := by
    intro hU
    have h := hUA U hU
    obtain ⟨v, hv⟩ := hUne
    exact Finset.disjoint_left.mp h hv hv
  have hnew : DegreeCoreFamily G K s (insert U P) := by
    constructor
    · intro A hA B hB hne
      rcases Finset.mem_insert.mp hA with hAU | hAP
      · subst A
        rcases Finset.mem_insert.mp hB with hBU | hBP
        · exact (hne hBU.symm).elim
        · exact hUA B hBP
      · rcases Finset.mem_insert.mp hB with hBU | hBP
        · subst B
          exact (hUA A hAP).symm
        · exact hgood.1 A hAP B hBP hne
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact ⟨hUne, (Finset.card_le_card hUT).trans hTK, hUcore⟩
      · exact hgood.2 A hA
  have hmax' := hmax (insert U P) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnew⟩)
  rw [Finset.biUnion_insert] at hmax'
  dsimp only [id_eq] at hmax'
  rw [Finset.card_union_of_disjoint hUdisjoint] at hmax'
  have hpositive := Finset.card_pos.mpr hUne
  omega

end Erdos911
