import Erdos911.FiberPruning

namespace Erdos911

theorem card_subtype_finset_filter {A : Type*} (S : Finset A) (P : A → Prop) [DecidablePred P] :
    Fintype.card {x : ↥S // P x.val} = (S.filter P).card := by
  classical
  let e : {x : ↥S // P x.val} ≃ ↥(S.filter P) :=
    { toFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨x.val.property, x.property⟩⟩
      invFun := fun x => ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩, (Finset.mem_filter.mp x.property).2⟩
      left_inv := fun x => by cases x; rfl
      right_inv := fun x => by cases x; rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

/-- Count a dependent product only over the fibers whose base has a
specified property. This is used for events touching a fixed row. -/
theorem restricted_sigma_product_card_le {I C : Type*} [Fintype I] [Fintype C]
    (X : I → Type*) [∀ i, Fintype (X i)] (P : I → Prop) [DecidablePred P]
    (b k l : ℕ) (hP : Fintype.card {i // P i} ≤ b)
    (hX : ∀ i, Fintype.card (X i) ≤ k) (hC : Fintype.card C ≤ l) :
    Fintype.card {e : (Σ i, X i × C) // P e.1} ≤ b * (k * l) := by
  classical
  let e : {e : (Σ i, X i × C) // P e.1} ≃ (Σ i : {i // P i}, X i.val × C) :=
    { toFun := fun e => ⟨⟨e.val.1, e.property⟩, e.val.2⟩
      invFun := fun e => ⟨⟨e.1.val, e.2⟩, e.1.property⟩
      left_inv := fun e => by cases e; rfl
      right_inv := fun e => by cases e; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  calc
    (∑ i : {i // P i}, Fintype.card (X i.val × C)) ≤ ∑ _i : {i // P i}, k * l := by
      apply Finset.sum_le_sum
      intro i _
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul (hX i.val) hC
    _ = Fintype.card {i // P i} * (k * l) := by simp
    _ ≤ b * (k * l) := Nat.mul_le_mul_right _ hP

end Erdos911
