import Erdos911.NearRegularPruningParameters
import Erdos911.MixedBlockPacking

open Filter Asymptotics

namespace Erdos911

theorem blockEdgeUnion_union {V : Type*} [DecidableEq V]
    (P Q : Finset (RectangleBlock V)) : blockEdgeUnion (P ∪ Q) = blockEdgeUnion P ∪ blockEdgeUnion Q := by
  classical
  ext e
  simp only [mem_blockEdgeUnion, Finset.mem_union]
  aesop

theorem blockResidual_union {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) (P Q : Finset (RectangleBlock V)) :
    blockResidual H (P ∪ Q) = blockResidual (blockResidual H P) Q := by
  unfold blockResidual
  rw [SimpleGraph.deleteEdges_deleteEdges, blockEdgeUnion_union]
  simp only [Finset.coe_union]

theorem near_regular_block_sizes_ordered_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, baselineBlockSize d ≤ nearRegularBlockSize d := by
  have hlimit := (isLittleO_log_rpow_rpow_atTop (4 : ℕ)
    (show (0 : ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (hlimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast (show Nat.ceil x₀ ≤ d by omega)))
  have hpower : (Real.log d) ^ 4 ≤ (d : ℝ) ^ (1 / 4 : ℝ) := by
    have h' := (div_lt_iff₀ (Real.rpow_pos_of_pos hdpos (1 / 4 : ℝ))).mp h
    simpa only [Real.rpow_natCast, one_mul] using h'.le
  exact Nat.ceil_mono hpower

theorem exists_two_scale_residual_blocks {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (q₁ q₂ : ℕ) (ρ₁ ρ₂ : ℝ)
    (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) (hq : q₁ ≤ q₂) :
    ∃ P Q : Finset (RectangleBlock V),
      ValidBlockPacking H q₁ ρ₁ P ∧ ValidBlockPacking H q₂ ρ₂ Q ∧
      Disjoint (blockEdgeUnion P) (blockEdgeUnion Q) ∧
      BoundedEdgeBlocks (P ∪ Q) (q₂ * q₂) ∧
      (∀ A B : Finset V, A.card = q₁ → B.card = q₁ → Disjoint A B →
        (crossEdges (blockResidual H (P ∪ Q)) A B : ℝ) ≤ ρ₁ * q₁ * q₁) ∧
      (∀ A B : Finset V, A.card = q₂ → B.card = q₂ → Disjoint A B →
        (crossEdges (blockResidual H (P ∪ Q)) A B : ℝ) ≤ ρ₂ * q₂ * q₂) := by
  obtain ⟨P, Q, hP, hQ, hcross, hbound, hfirst, hsecond⟩ :=
    exists_two_scale_bounded_blocks H q₁ q₂ ρ₁ ρ₂ hρ₁ hρ₂
  refine ⟨P, Q, hP, hQ.mono (blockResidual_le H P), hcross, ?_, ?_, ?_⟩
  · simpa only [max_eq_right (Nat.mul_le_mul hq hq)] using hbound
  · simpa only [blockResidual_union] using hfirst
  · simpa only [blockResidual_union] using hsecond

end Erdos911
