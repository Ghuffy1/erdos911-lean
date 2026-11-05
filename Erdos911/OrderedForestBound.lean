import Erdos911.OrderedForestSampling
import Erdos911.ForestWeights

namespace Erdos911

theorem degree_sum_injective_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (x : Fin n → W) (hx : Function.Injective x) :
    (∑ i, H.degree (x i)) ≤ 2 * H.edgeFinset.card := by
  classical
  have himage : (∑ w ∈ Finset.univ.image x, H.degree w) = ∑ i, H.degree (x i) :=
    Finset.sum_image (fun i _ j _ h => hx h)
  rw [← himage]
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Nat.zero_le _))
  exact H.sum_degrees_eq_twice_card_edges.le

theorem active_parent_degree_pos {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (x : Fin n → W)
    (hedges : ∀ i j, parent i = some j → H.Adj (initialSegment x i j) (x i))
    (j : Fin n) (hj : 0 < parentFiberCard parent (some j)) : 0 < H.degree (x j) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hj
  have hparent : orderedParent parent i = some j := (Finset.mem_filter.mp hi).2
  cases hp : parent i with
  | none => simp [orderedParent, hp] at hparent
  | some k =>
    have heq : (⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ : Fin n) = j := by
      simpa only [orderedParent, hp, Option.map_some, Option.some.injEq] using hparent
    have hadj := hedges i k hp
    change H.Adj (x ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) (x i) at hadj
    rw [heq] at hadj
    exact hadj.degree_pos_left

theorem forestAssignmentWeight_inverse {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (x : Fin n → W)
    (hedges : ∀ i j, parent i = some j → H.Adj (initialSegment x i j) (x i)) :
    forestAssignmentWeight H parent x =
      1 / ((Fintype.card W : ℝ) ^ parentFiberCard parent none *
        ∏ j, (H.degree (x j) : ℝ) ^ parentFiberCard parent (some j)) := by
  rw [forestAssignmentWeight_eq_grouped H parent x hedges]
  simp only [one_div, inv_pow, Finset.prod_inv_distrib, mul_inv_rev]
  exact mul_comm _ _

noncomputable def forestEmbeddingBound {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) : ℝ :=
  (Fintype.card W : ℝ) ^ parentFiberCard parent none *
    ((2 * H.edgeFinset.card : ℝ) / (∑ j, parentFiberCard parent (some j))) ^
      (∑ j, parentFiberCard parent (some j)) *
        ∏ j, (parentFiberCard parent (some j) : ℝ) ^ parentFiberCard parent (some j)

theorem forestEmbeddingBound_pos {W : Type*} [Fintype W] [Nonempty W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val)) (hH : 0 < H.edgeFinset.card)
    (hS : 0 < ∑ j, parentFiberCard parent (some j)) : 0 < forestEmbeddingBound H parent := by
  have hN : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hM : (0 : ℝ) < (2 * H.edgeFinset.card : ℝ) := by positivity
  have hSreal : (0 : ℝ) < (∑ j, parentFiberCard parent (some j) : ℕ) := by exact_mod_cast hS
  have hfactor : 0 < ∏ j, (parentFiberCard parent (some j) : ℝ) ^
      parentFiberCard parent (some j) := by
    apply Finset.prod_pos
    intro j _
    by_cases hj : parentFiberCard parent (some j) = 0
    · simp [hj]
    · apply pow_pos
      exact_mod_cast Nat.pos_of_ne_zero hj
  unfold forestEmbeddingBound
  exact mul_pos (mul_pos (pow_pos hN _) (pow_pos (div_pos hM hSreal) _)) hfactor

theorem forestAssignmentWeight_lower_bound {W : Type*} [Fintype W] [Nonempty W]
    [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val))
    (hH : 0 < H.edgeFinset.card) (hS : 0 < ∑ j, parentFiberCard parent (some j))
    (x : Fin n → W) (hx : Function.Injective x)
    (hedges : ∀ i j, parent i = some j → H.Adj (initialSegment x i j) (x i)) :
    1 / forestEmbeddingBound H parent ≤ forestAssignmentWeight H parent x := by
  have hdegree : (∑ j, (H.degree (x j) : ℝ)) ≤ (2 * H.edgeFinset.card : ℝ) := by
    exact_mod_cast degree_sum_injective_le H x hx
  have hprod := weighted_degree_product_bound (fun j => (H.degree (x j) : ℝ))
    (fun j => parentFiberCard parent (some j)) (2 * H.edgeFinset.card)
    (fun _ => Nat.cast_nonneg _) hS hdegree
  have hN : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have hdenpos : 0 < (Fintype.card W : ℝ) ^ parentFiberCard parent none *
      ∏ j, (H.degree (x j) : ℝ) ^ parentFiberCard parent (some j) := by
    apply mul_pos (pow_pos hN _)
    apply Finset.prod_pos
    intro j _
    by_cases hj : parentFiberCard parent (some j) = 0
    · simp [hj]
    · apply pow_pos
      exact_mod_cast active_parent_degree_pos H parent x hedges j (Nat.pos_of_ne_zero hj)
  rw [forestAssignmentWeight_inverse H parent x hedges]
  apply (div_le_div_iff₀ (forestEmbeddingBound_pos H parent hH hS) hdenpos).mpr
  simp only [one_mul]
  unfold forestEmbeddingBound
  have hscale := mul_le_mul_of_nonneg_left hprod
    (pow_nonneg hN.le (parentFiberCard parent none))
  simpa only [mul_assoc] using hscale

/-- The spanning-forest embedding count for an ordered parent structure.
Every injection preserving its parent edges receives the required mass in
the finite sampling distribution. -/
theorem ordered_forest_embedding_count {W : Type*} [Fintype W] [Nonempty W]
    [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val))
    (hH : 0 < H.edgeFinset.card) (hS : 0 < ∑ j, parentFiberCard parent (some j))
    (E : Finset (Fin n → W))
    (hinjective : ∀ x ∈ E, Function.Injective x)
    (hedges : ∀ x ∈ E, ∀ i j, parent i = some j → H.Adj (initialSegment x i j) (x i)) :
    (E.card : ℝ) ≤ forestEmbeddingBound H parent := by
  have hcount := card_mul_le_of_weight_lower_bound (forestAssignmentWeight H parent) E
    (1 / forestEmbeddingBound H parent) (forestAssignmentWeight_nonneg H parent)
    (forestAssignmentWeight_sum_le_one H parent)
    (fun x hx => forestAssignmentWeight_lower_bound H parent hH hS x
      (hinjective x hx) (hedges x hx))
  apply (div_le_one (forestEmbeddingBound_pos H parent hH hS)).mp
  simpa only [div_eq_mul_inv, one_mul] using hcount

theorem ordered_forest_embedding_count_of_child_bound {W : Type*} [Fintype W]
    [Nonempty W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj] {n : ℕ}
    (parent : (i : Fin n) → Option (Fin i.val))
    (hH : 0 < H.edgeFinset.card) (hS : 0 < ∑ j, parentFiberCard parent (some j))
    (D : ℕ) (hD : ∀ j, parentFiberCard parent (some j) ≤ D)
    (E : Finset (Fin n → W)) (hinjective : ∀ x ∈ E, Function.Injective x)
    (hedges : ∀ x ∈ E, ∀ i j, parent i = some j → H.Adj (initialSegment x i j) (x i)) :
    (E.card : ℝ) ≤ (Fintype.card W : ℝ) ^ parentFiberCard parent none *
      ((2 * H.edgeFinset.card : ℝ) / (∑ j, parentFiberCard parent (some j))) ^
        (∑ j, parentFiberCard parent (some j)) *
          (D : ℝ) ^ (∑ j, parentFiberCard parent (some j)) := by
  apply (ordered_forest_embedding_count H parent hH hS E hinjective hedges).trans
  unfold forestEmbeddingBound
  exact mul_le_mul_of_nonneg_left
    (child_degree_product_le (fun j => parentFiberCard parent (some j)) D hD) (by positivity)

end Erdos911
