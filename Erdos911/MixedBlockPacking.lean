import Erdos911.RepeatedBlockCounting

namespace Erdos911

theorem BoundedEdgeBlocks.mono {V : Type*} {P : Finset (RectangleBlock V)} {M N : ℕ}
    (hP : BoundedEdgeBlocks P M) (hMN : M ≤ N) : BoundedEdgeBlocks P N :=
  ⟨fun B hB => (hP.1 B hB).trans hMN, hP.2⟩

theorem BoundedEdgeBlocks.union {V : Type*} [DecidableEq V]
    {P Q : Finset (RectangleBlock V)} {M N : ℕ}
    (hP : BoundedEdgeBlocks P M) (hQ : BoundedEdgeBlocks Q N)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q)) :
    BoundedEdgeBlocks (P ∪ Q) (max M N) := by
  classical
  have hsub {S : Finset (RectangleBlock V)} {B : RectangleBlock V} (hB : B ∈ S) :
      B.edges ⊆ blockEdgeUnion S := by
    intro e he
    exact (mem_blockEdgeUnion S e).mpr ⟨B, hB, he⟩
  constructor
  · intro B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · exact (hP.1 B hB).trans (Nat.le_max_left _ _)
    · exact (hQ.1 B hB).trans (Nat.le_max_right _ _)
  · intro B hB C hC hBC
    rcases Finset.mem_union.mp hB with hB | hB <;>
      rcases Finset.mem_union.mp hC with hC | hC
    · exact hP.2 hB hC hBC
    · exact hcross.mono (hsub hB) (hsub hC)
    · exact hcross.symm.mono (hsub hB) (hsub hC)
    · exact hQ.2 hB hC hBC

/-- The existing two-scale extraction gives a single edge-disjoint family
with a common upper bound on block edge counts. -/
theorem exists_two_scale_bounded_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q₁ q₂ : ℕ) (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    ∃ P₁ P₂ : Finset (RectangleBlock V),
      ValidBlockPacking G q₁ ρ₁ P₁ ∧
      ValidBlockPacking (blockResidual G P₁) q₂ ρ₂ P₂ ∧
      Disjoint (blockEdgeUnion P₁) (blockEdgeUnion P₂) ∧
      BoundedEdgeBlocks (P₁ ∪ P₂) (max (q₁ * q₁) (q₂ * q₂)) ∧
      (∀ A B : Finset V, A.card = q₁ → B.card = q₁ → Disjoint A B →
        (crossEdges (blockResidual (blockResidual G P₁) P₂) A B : ℝ) ≤ ρ₁ * q₁ * q₁) ∧
      (∀ A B : Finset V, A.card = q₂ → B.card = q₂ → Disjoint A B →
        (crossEdges (blockResidual (blockResidual G P₁) P₂) A B : ℝ) ≤ ρ₂ * q₂ * q₂) := by
  obtain ⟨P₁, P₂, hP₁, hP₂, hcross, hres₁, hres₂⟩ :=
    exists_two_scale_block_packing G q₁ q₂ ρ₁ ρ₂ hρ₁ hρ₂
  exact ⟨P₁, P₂, hP₁, hP₂, hcross,
    hP₁.boundedEdgeBlocks.union hP₂.boundedEdgeBlocks hcross, hres₁, hres₂⟩

end Erdos911
