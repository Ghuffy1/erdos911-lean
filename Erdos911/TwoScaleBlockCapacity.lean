import Erdos911.BlockRedConditions

namespace Erdos911

theorem validBlockPackings_disjoint {W : Type*} [DecidableEq W]
    {H : SimpleGraph W} {q : ℕ} {ρ : ℝ} {P Q : Finset (RectangleBlock W)}
    (hP : ValidBlockPacking H q ρ P) (hρ : 0 ≤ ρ)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q)) : Disjoint P Q := by
  classical
  apply Finset.disjoint_left.mpr
  intro B hBP hBQ
  have hpositive : (0 : ℝ) < B.edges.card :=
    (by positivity : (0 : ℝ) ≤ ρ * q * q).trans_lt (hP.1 B hBP).2.2.2.2
  obtain ⟨e, he⟩ := Finset.card_pos.mp (show 0 < B.edges.card by exact_mod_cast hpositive)
  exact Finset.disjoint_left.mp hcross
    ((mem_blockEdgeUnion P e).mpr ⟨B, hBP, he⟩)
    ((mem_blockEdgeUnion Q e).mpr ⟨B, hBQ, he⟩)

noncomputable def twoScaleBlockCapacity {W : Type*} [DecidableEq W]
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (σ : ℝ) : ↥(P ∪ Q) → ℝ := by
  classical
  exact fun B => if B.val ∈ P then 2 * σ * q₁ else 2 * σ * q₂

theorem twoScaleBlockCapacity_nonneg {W : Type*} [DecidableEq W]
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (σ : ℝ) (hσ : 0 ≤ σ)
    (B : ↥(P ∪ Q)) : 0 ≤ twoScaleBlockCapacity P Q q₁ q₂ σ B := by
  classical
  unfold twoScaleBlockCapacity
  split_ifs <;> positivity

theorem twoScaleBlockCapacity_sum {W : Type*} [DecidableEq W]
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (σ : ℝ) (hPQ : Disjoint P Q) :
    (∑ B : ↥(P ∪ Q), twoScaleBlockCapacity P Q q₁ q₂ σ B) =
      2 * σ * q₁ * P.card + 2 * σ * q₂ * Q.card := by
  classical
  let c : RectangleBlock W → ℝ := fun B => if B ∈ P then 2 * σ * q₁ else 2 * σ * q₂
  have hsum : (∑ B : ↥(P ∪ Q), twoScaleBlockCapacity P Q q₁ q₂ σ B) =
      ∑ B ∈ P ∪ Q, c B := by
    calc
      _ = ∑ B : ↥(P ∪ Q), c B.val := by
        apply Finset.sum_congr rfl
        intro B _
        unfold twoScaleBlockCapacity c
        split_ifs <;> rfl
      _ = _ := Finset.sum_coe_sort (P ∪ Q) c
  rw [hsum, Finset.sum_union hPQ]
  have hleft : (∑ B ∈ P, if B ∈ P then 2 * σ * q₁ else 2 * σ * q₂) =
      2 * σ * q₁ * P.card := by
    rw [Finset.sum_congr rfl (fun B hB => ite_eq_left hB)]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hright : (∑ B ∈ Q, if B ∈ P then 2 * σ * q₁ else 2 * σ * q₂) =
      2 * σ * q₂ * Q.card := by
    rw [Finset.sum_congr rfl (fun B hB => ite_eq_right
      (fun hBP => Finset.disjoint_left.mp hPQ hBP hB))]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact congrArg₂ (· + ·) hleft hright

theorem twoScaleBlockCapacity_bounds_copies {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (ρ₁ ρ₂ σ : ℝ)
    (hP : ValidBlockPacking H q₁ ρ₁ P) (hQ : ValidBlockPacking H q₂ ρ₂ Q)
    (hσ : 0 ≤ σ)
    (hlocal : ∀ U : Finset V, U.card ≤ 2 * max q₁ q₂ →
      ((G.induce (U : Set V)).edgeSet.ncard : ℝ) ≤ σ * U.card)
    (f : G.Copy H) (B : ↥(P ∪ Q)) :
    ((copyRawEdges f ∩ B.val.edges).card : ℝ) ≤ twoScaleBlockCapacity P Q q₁ q₂ σ B := by
  classical
  rw [copyRawEdges_block_inter_card]
  unfold twoScaleBlockCapacity
  split_ifs with hB
  · apply block_copy_capacity_le G H f q₁ ρ₁ σ hσ B.val (hP.1 B.val hB)
    intro U hU
    exact hlocal U (hU.trans (Nat.mul_le_mul_left 2 (Nat.le_max_left q₁ q₂)))
  · have hBQ : B.val ∈ Q := (Finset.mem_union.mp B.property).resolve_left hB
    apply block_copy_capacity_le G H f q₂ ρ₂ σ hσ B.val (hQ.1 B.val hBQ)
    intro U hU
    exact hlocal U (hU.trans (Nat.mul_le_mul_left 2 (Nat.le_max_right q₁ q₂)))

theorem twoScaleBlockCapacity_total_bound {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (ρ₁ ρ₂ σ : ℝ)
    (hP : ValidBlockPacking H q₁ ρ₁ P) (hQ : ValidBlockPacking H q₂ ρ₂ Q)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q))
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hσ : 0 ≤ σ) :
    (∑ B : ↥(P ∪ Q), twoScaleBlockCapacity P Q q₁ q₂ σ B) ≤
      2 * σ * H.edgeFinset.card / (ρ₁ * q₁) +
        2 * σ * H.edgeFinset.card / (ρ₂ * q₂) := by
  have hscaled (S : Finset (RectangleBlock W)) (q : ℕ) (ρ : ℝ)
      (hS : ValidBlockPacking H q ρ S) (hq : 0 < q) (hρ : 0 < ρ) :
      2 * σ * q * S.card ≤ 2 * σ * H.edgeFinset.card / (ρ * q) := by
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
    have hbound := validBlockPacking_capacity_bound H q ρ S hS (by positivity)
      (fun _ => 2 * σ * q) (2 * σ * q) (by positivity) (fun _ _ => le_rfl)
    have heq : (2 * σ * q) * H.edgeFinset.card / (ρ * q * q) =
        2 * σ * H.edgeFinset.card / (ρ * q) := by field_simp
    simp only [Finset.sum_const, nsmul_eq_mul] at hbound
    rw [heq] at hbound
    simpa only [mul_comm] using hbound
  rw [twoScaleBlockCapacity_sum P Q q₁ q₂ σ (validBlockPackings_disjoint hP hρ₁.le hcross)]
  exact add_le_add (hscaled P q₁ ρ₁ hP hq₁ hρ₁) (hscaled Q q₂ ρ₂ hQ hq₂ hρ₂)

end Erdos911
