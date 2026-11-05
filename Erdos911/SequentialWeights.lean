import Erdos911.FiniteHolder
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod

namespace Erdos911

def initialSegment {A : Type*} {n : ℕ} (x : Fin n → A) (i : Fin n) : Fin i.val → A :=
  fun j => x ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

noncomputable def sequentialWeight {A : Type*} : {n : ℕ} →
    ((i : Fin n) → (Fin i.val → A) → A → ℝ) → (Fin n → A) → ℝ
  | 0, _, _ => 1
  | n + 1, F, x =>
    sequentialWeight (fun i : Fin n => F i.castSucc) (Fin.init x) *
      F (Fin.last n) (Fin.init x) (x (Fin.last n))

theorem sequentialWeight_snoc {A : Type*} {n : ℕ}
    (F : (i : Fin (n + 1)) → (Fin i.val → A) → A → ℝ)
    (x : Fin n → A) (a : A) :
    sequentialWeight F (Fin.snoc x a) =
      sequentialWeight (fun i : Fin n => F i.castSucc) x * F (Fin.last n) x a := by
  simp only [sequentialWeight, Fin.init_snoc, Fin.snoc_last]

theorem sequentialWeight_nonneg {A : Type*} {n : ℕ}
    (F : (i : Fin n) → (Fin i.val → A) → A → ℝ)
    (hF : ∀ i x a, 0 ≤ F i x a) (x : Fin n → A) : 0 ≤ sequentialWeight F x := by
  induction n with
  | zero => norm_num [sequentialWeight]
  | succ n ih =>
    exact mul_nonneg (ih (fun i => F i.castSucc) (fun i => hF i.castSucc) (Fin.init x))
      (hF (Fin.last n) (Fin.init x) (x (Fin.last n)))

theorem sequentialWeight_eq_prod {A : Type*} {n : ℕ}
    (F : (i : Fin n) → (Fin i.val → A) → A → ℝ) (x : Fin n → A) :
    sequentialWeight F x = ∏ i, F i (initialSegment x i) (x i) := by
  induction n with
  | zero => simp [sequentialWeight]
  | succ n ih =>
    rw [sequentialWeight, ih, Fin.prod_univ_castSucc]
    rfl

/-- A sequence of finite nonnegative transition rows of mass at most one
defines an assignment weight of total mass at most one. -/
theorem sum_sequentialWeight_le_one {A : Type*} [Fintype A] {n : ℕ}
    (F : (i : Fin n) → (Fin i.val → A) → A → ℝ)
    (hF : ∀ i x a, 0 ≤ F i x a) (hrow : ∀ i x, (∑ a, F i x a) ≤ 1) :
    (∑ x : Fin n → A, sequentialWeight F x) ≤ 1 := by
  induction n with
  | zero => simp [sequentialWeight]
  | succ n ih =>
    let e : ((Fin n → A) × A) ≃ (Fin (n + 1) → A) :=
      (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => A))
    calc
      (∑ x : Fin (n + 1) → A, sequentialWeight F x) =
          ∑ z : (Fin n → A) × A, sequentialWeight F (Fin.snoc z.1 z.2) :=
        (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
      _ = ∑ x : Fin n → A, ∑ a : A,
          sequentialWeight (fun i : Fin n => F i.castSucc) x * F (Fin.last n) x a := by
        rw [Fintype.sum_prod_type]
        simp only [sequentialWeight_snoc]
      _ = ∑ x : Fin n → A, sequentialWeight (fun i : Fin n => F i.castSucc) x *
          (∑ a : A, F (Fin.last n) x a) := by simp only [Finset.mul_sum]
      _ ≤ ∑ x : Fin n → A, sequentialWeight (fun i : Fin n => F i.castSucc) x := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_of_le_one_right
          (sequentialWeight_nonneg _ (fun i => hF i.castSucc) x) (hrow (Fin.last n) x)
      _ ≤ 1 := ih (fun i : Fin n => F i.castSucc) (fun i => hF i.castSucc)
        (fun i => hrow i.castSucc)

theorem card_mul_le_of_weight_lower_bound {A : Type*} [Fintype A]
    (w : A → ℝ) (S : Finset A) (c : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hmass : (∑ a, w a) ≤ 1)
    (hlower : ∀ a ∈ S, c ≤ w a) : (S.card : ℝ) * c ≤ 1 := by
  classical
  calc
    (S.card : ℝ) * c = ∑ _a ∈ S, c := by simp
    _ ≤ ∑ a ∈ S, w a := Finset.sum_le_sum hlower
    _ ≤ ∑ a, w a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => hw a)
    _ ≤ 1 := hmass

end Erdos911
