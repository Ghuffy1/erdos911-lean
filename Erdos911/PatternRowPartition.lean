import Erdos911.TargetPatternGraph

namespace Erdos911

theorem patternComponentRows_partition {A R : Type*}
    [Fintype A] [Fintype R] [DecidableEq R]
    (T : R → Finset A) (B U : Finset R) (hUB : U ⊆ B)
    (hne : ∀ y ∈ B, (T y).Nonempty)
    [Fintype (patternCliqueGraph T U).ConnectedComponent] :
    (∑ c : (patternCliqueGraph T U).ConnectedComponent,
      (U ∩ patternComponentRows T B (patternCliqueGraph T U) c).card) = U.card := by
  classical
  let P := patternCliqueGraph T U
  let F := fun c : P.ConnectedComponent => U ∩ patternComponentRows T B P c
  have hdisj : ((Finset.univ : Finset P.ConnectedComponent) : Set P.ConnectedComponent).PairwiseDisjoint F := by
    intro c _ d _ hcd
    exact (patternComponentRows_disjoint T B P hne c d hcd).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hcover : (Finset.univ.biUnion F) = U := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hy
      exact (Finset.mem_inter.mp hc).1
    · intro hy
      obtain ⟨x, hx⟩ := hne y (hUB hy)
      apply Finset.mem_biUnion.mpr
      refine ⟨P.connectedComponentMk x, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hy, ?_⟩⟩
      apply Finset.mem_filter.mpr
      exact ⟨hUB hy, patternCliqueGraph_row_component T U y hy x hx⟩
  exact (Finset.card_biUnion hdisj).symm.trans (congrArg Finset.card hcover)

theorem connectedComponent_count_le {A : Type*} [Fintype A]
    (P : SimpleGraph A) [Fintype P.ConnectedComponent] :
    Fintype.card P.ConnectedComponent ≤ Fintype.card A := by
  classical
  exact Fintype.card_le_of_surjective P.connectedComponentMk Quot.mk_surjective

end Erdos911
