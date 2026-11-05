import Erdos911.BlockCapacity

namespace Erdos911

noncomputable def blockResidual {V : Type*} (G : SimpleGraph V)
    (P : Finset (RectangleBlock V)) : SimpleGraph V :=
  G.deleteEdges (blockEdgeUnion P : Set (Sym2 V))

theorem blockResidual_le {V : Type*} (G : SimpleGraph V) (P : Finset (RectangleBlock V)) :
    blockResidual G P ≤ G :=
  G.deleteEdges_le _

/-- The two scales have disjoint edge sets, and the final residual satisfies
both rectangular sparsity conditions. -/
theorem exists_two_scale_block_packing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q₁ q₂ : ℕ) (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ P₁ P₂ : Finset (RectangleBlock V),
      ValidBlockPacking G q₁ ρ₁ P₁ ∧
      ValidBlockPacking (blockResidual G P₁) q₂ ρ₂ P₂ ∧
      Disjoint (blockEdgeUnion P₁) (blockEdgeUnion P₂) ∧
      (∀ A B : Finset V, A.card = q₁ → B.card = q₁ → Disjoint A B →
        (crossEdges (blockResidual (blockResidual G P₁) P₂) A B : ℝ) ≤ ρ₁ * q₁ * q₁) ∧
      (∀ A B : Finset V, A.card = q₂ → B.card = q₂ → Disjoint A B →
        (crossEdges (blockResidual (blockResidual G P₁) P₂) A B : ℝ) ≤ ρ₂ * q₂ * q₂) := by
  classical
  obtain ⟨P₁, hP₁, hres₁⟩ := exists_dense_block_packing G q₁ ρ₁ hρ₁
  let J₁ := blockResidual G P₁
  obtain ⟨P₂, hP₂, hres₂⟩ := exists_dense_block_packing J₁ q₂ ρ₂ hρ₂
  have hdis : Disjoint (blockEdgeUnion P₁) (blockEdgeUnion P₂) := by
    apply Finset.disjoint_left.mpr
    intro e he₁ he₂
    have heJ := validBlockPacking_edgeUnion_subset J₁ q₂ ρ₂ P₂ hP₂ he₂
    have heSet : e ∈ J₁.edgeSet := (SimpleGraph.mem_edgeFinset).mp heJ
    dsimp only [J₁, blockResidual] at heSet
    rw [G.edgeSet_deleteEdges] at heSet
    exact heSet.2 he₁
  refine ⟨P₁, P₂, hP₁, hP₂, hdis, ?_, hres₂⟩
  intro A B hA hB hAB
  have hmono : (crossEdges (blockResidual J₁ P₂) A B : ℝ) ≤ crossEdges J₁ A B := by
    exact_mod_cast crossEdges_mono (blockResidual_le J₁ P₂) A B
  exact hmono.trans (hres₁ A B hA hB hAB)

end Erdos911
