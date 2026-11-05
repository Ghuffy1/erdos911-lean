import Erdos911.SequentialWeights
import Mathlib.Data.Finset.Powerset

namespace Erdos911

def earlierIndex {n : ℕ} (i : Fin n) (j : Fin i.val) : Fin n :=
  ⟨j.val, j.isLt.trans i.isLt⟩

noncomputable def collisionIndices {A : Type*} {n : ℕ} (f : Fin n → A) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j : Fin i.val, f (earlierIndex i j) = f i)

theorem mem_collisionIndices {A : Type*} {n : ℕ} (f : Fin n → A) (i : Fin n) :
    i ∈ collisionIndices f ↔ ∃ j : Fin i.val, f (earlierIndex i j) = f i := by
  classical
  simp only [collisionIndices, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev EarlierParents {n : ℕ} (J : Finset (Fin n)) := (i : ↥J) → Fin i.val.val

theorem earlierParents_card_le {n : ℕ} (J : Finset (Fin n)) :
    Fintype.card (EarlierParents J) ≤ n ^ J.card := by
  classical
  change Fintype.card ((i : ↥J) → Fin i.val.val) ≤ _
  rw [Fintype.card_pi]
  calc
    (∏ i : ↥J, Fintype.card (Fin i.val.val)) ≤ ∏ _i : ↥J, n := by
      apply Finset.prod_le_prod
      intro i _
      simpa only [Fintype.card_fin] using i.val.isLt.le
    _ = n ^ J.card := by simp

noncomputable def parentConstrainedLabels {A : Type*} [Fintype A] {n : ℕ}
    (J : Finset (Fin n)) (p : EarlierParents J) : Finset (Fin n → A) := by
  classical
  exact Finset.univ.filter (fun f => ∀ i : ↥J, f i.val = f (earlierIndex i.val (p i)))

/-- Values at positions without an earlier-parent constraint determine all
values, since each constrained position refers to a strictly earlier one. -/
theorem earlier_parent_labels_determined {A : Type*} {n : ℕ}
    (J : Finset (Fin n)) (p : EarlierParents J) (f g : Fin n → A)
    (hf : ∀ i : ↥J, f i.val = f (earlierIndex i.val (p i)))
    (hg : ∀ i : ↥J, g i.val = g (earlierIndex i.val (p i)))
    (hfree : ∀ i, i ∉ J → f i = g i) : f = g := by
  have hall : ∀ k (hk : k < n), f ⟨k, hk⟩ = g ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let i : Fin n := ⟨k, hk⟩
      by_cases hi : i ∈ J
      · rw [hf ⟨i, hi⟩, hg ⟨i, hi⟩]
        exact ih (p ⟨i, hi⟩).val (p ⟨i, hi⟩).isLt ((p ⟨i, hi⟩).isLt.trans hk)
      · exact hfree i hi
  funext i
  exact hall i.val i.isLt

theorem parentConstrainedLabels_card_le {A : Type*} [Fintype A] {n : ℕ}
    (J : Finset (Fin n)) (p : EarlierParents J) :
    (parentConstrainedLabels (A := A) J p).card ≤ Fintype.card A ^ (n - J.card) := by
  classical
  let encode : ↥(parentConstrainedLabels (A := A) J p) → (↥(Finset.univ \ J) → A) :=
    fun f i => f.val i.val
  have hinj : Function.Injective encode := by
    intro f g heq
    apply Subtype.ext
    apply earlier_parent_labels_determined J p f.val g.val
    · exact (Finset.mem_filter.mp f.property).2
    · exact (Finset.mem_filter.mp g.property).2
    · intro i hi
      exact congrFun heq ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have h := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_fun, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, Fintype.card_fin] using h

noncomputable def manyCollisionLabels (A : Type*) [Fintype A] (n r : ℕ) : Finset (Fin n → A) := by
  classical
  exact Finset.univ.filter (fun f => r ≤ (collisionIndices f).card)

/-- At least r sequential label collisions can be encoded by r positions,
an earlier parent for each, and labels only at the remaining positions. -/
theorem manyCollisionLabels_card_le (A : Type*) [Fintype A] (n r : ℕ) :
    (manyCollisionLabels A n r).card ≤
      2 ^ n * n ^ r * Fintype.card A ^ (n - r) := by
  classical
  let candidates : Finset (Fin n → A) := ((Finset.univ : Finset (Fin n)).powersetCard r).biUnion
    (fun J => (Finset.univ : Finset (EarlierParents J)).biUnion
      (fun p => parentConstrainedLabels J p))
  have hcover : manyCollisionLabels A n r ⊆ candidates := by
    intro f hf
    have hr : r ≤ (collisionIndices f).card := (Finset.mem_filter.mp hf).2
    obtain ⟨J, hJ, hJr⟩ := Finset.exists_subset_card_eq hr
    have hex (i : ↥J) : ∃ j : Fin i.val.val, f (earlierIndex i.val j) = f i.val :=
      (mem_collisionIndices f i.val).mp (hJ i.property)
    choose p hp using hex
    apply Finset.mem_biUnion.mpr
    refine ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hJr⟩, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact fun i => (hp i).symm
  have hinner (J : Finset (Fin n)) (hJ : J ∈ (Finset.univ : Finset (Fin n)).powersetCard r) :
      ((Finset.univ : Finset (EarlierParents J)).biUnion
        (fun p => parentConstrainedLabels (A := A) J p)).card ≤
      n ^ r * Fintype.card A ^ (n - r) := by
    have hJr := (Finset.mem_powersetCard.mp hJ).2
    calc
      _ ≤ ∑ p : EarlierParents J, (parentConstrainedLabels (A := A) J p).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _p : EarlierParents J, Fintype.card A ^ (n - J.card) :=
        Finset.sum_le_sum (fun p _ => parentConstrainedLabels_card_le J p)
      _ = Fintype.card (EarlierParents J) * Fintype.card A ^ (n - J.card) := by simp
      _ ≤ n ^ J.card * Fintype.card A ^ (n - J.card) :=
        Nat.mul_le_mul_right _ (earlierParents_card_le J)
      _ = _ := by rw [hJr]
  calc
    _ ≤ candidates.card := Finset.card_le_card hcover
    _ ≤ ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        ((Finset.univ : Finset (EarlierParents J)).biUnion
          (fun p => parentConstrainedLabels (A := A) J p)).card := Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ (Finset.univ : Finset (Fin n)).powersetCard r, n ^ r * Fintype.card A ^ (n - r) :=
      Finset.sum_le_sum hinner
    _ = ((Finset.univ : Finset (Fin n)).powersetCard r).card * (n ^ r * Fintype.card A ^ (n - r)) := by simp
    _ ≤ 2 ^ n * (n ^ r * Fintype.card A ^ (n - r)) := by
      apply Nat.mul_le_mul_right
      have hsub : (Finset.univ : Finset (Fin n)).powersetCard r ⊆ Finset.univ.powerset := by
        intro J hJ
        exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hJ).1
      have h := Finset.card_le_card hsub
      simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using h
    _ = _ := by ring

end Erdos911
