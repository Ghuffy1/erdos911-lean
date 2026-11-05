import Erdos911.UniformLabelRestriction

namespace Erdos911

noncomputable def repeatedIndices {A : Type*} {n : ℕ} (f : Fin n → A) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j, j ≠ i ∧ f j = f i)

theorem mem_repeatedIndices {A : Type*} {n : ℕ} (f : Fin n → A) (i : Fin n) :
    i ∈ repeatedIndices f ↔ ∃ j, j ≠ i ∧ f j = f i := by
  classical
  simp only [repeatedIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem collisionIndices_subset_repeated {A : Type*} {n : ℕ} (f : Fin n → A) :
    collisionIndices f ⊆ repeatedIndices f := by
  intro i hi
  obtain ⟨j, hj⟩ := (mem_collisionIndices f i).mp hi
  refine (mem_repeatedIndices f i).mpr ⟨earlierIndex i j, ?_, hj⟩
  intro heq
  have hval := congrArg Fin.val heq
  have hlt := j.isLt
  simp only [earlierIndex] at hval
  omega

theorem noncollision_label_injective {A : Type*} {n : ℕ} (f : Fin n → A)
    (i j : Fin n) (hi : i ∉ collisionIndices f) (hj : j ∉ collisionIndices f)
    (heq : f i = f j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · apply hj
    exact (mem_collisionIndices f j).mpr ⟨⟨i.val, hij⟩, heq⟩
  · apply hi
    exact (mem_collisionIndices f i).mpr ⟨⟨j.val, hji⟩, heq.symm⟩

/-- Every repeated label class has all but its first index counted as
collisions, so at most twice as many vertices have repeated labels. -/
theorem repeatedIndices_card_le_twice_collisions {A : Type*} {n : ℕ} (f : Fin n → A) :
    (repeatedIndices f).card ≤ 2 * (collisionIndices f).card := by
  classical
  let F := repeatedIndices f \ collisionIndices f
  have hex (i : ↥F) : ∃ j ∈ collisionIndices f, f j = f i.val := by
    have hiR := (Finset.mem_sdiff.mp i.property).1
    have hiC := (Finset.mem_sdiff.mp i.property).2
    obtain ⟨j, hji, heq⟩ := (mem_repeatedIndices f i.val).mp hiR
    have hjC : j ∈ collisionIndices f := by
      by_contra hn
      exact hji (noncollision_label_injective f j i.val hn hiC heq)
    exact ⟨j, hjC, heq⟩
  choose g hg heq using hex
  let p : ↥F → ↥(collisionIndices f) := fun i => ⟨g i, hg i⟩
  have hp : Function.Injective p := by
    intro i j hij
    apply Subtype.ext
    apply noncollision_label_injective f i.val j.val
      (Finset.mem_sdiff.mp i.property).2 (Finset.mem_sdiff.mp j.property).2
    have h := congrArg Subtype.val hij
    have h' : g i = g j := h
    exact (heq i).symm.trans ((congrArg f h').trans (heq j))
  have hcard : F.card ≤ (collisionIndices f).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective p hp
  have hsum := Finset.card_sdiff_add_card_eq_card (collisionIndices_subset_repeated f)
  change F.card + (collisionIndices f).card = (repeatedIndices f).card at hsum
  omega

noncomputable def repeatedVertices {V A : Type*} (S : Finset V) (f : V → A) : Finset V := by
  classical
  exact S.filter (fun v => ∃ w ∈ S, w ≠ v ∧ f w = f v)

theorem mem_repeatedVertices {V A : Type*} (S : Finset V) (f : V → A) (v : V) :
    v ∈ repeatedVertices S f ↔ v ∈ S ∧ ∃ w ∈ S, w ≠ v ∧ f w = f v := by
  classical
  exact Finset.mem_filter

theorem repeatedVertices_card_eq_indices {V A : Type*} (S : Finset V) (f : V → A) :
    (repeatedVertices S f).card = (repeatedIndices (orderedSetLabels S f)).card := by
  classical
  symm
  apply Finset.card_bij (fun i _ => setLabelEmbedding S i)
  · intro i hi
    obtain ⟨j, hji, heq⟩ := (mem_repeatedIndices (orderedSetLabels S f) i).mp hi
    refine (mem_repeatedVertices S f _).mpr ⟨setLabelEmbedding_mem S i,
      setLabelEmbedding S j, setLabelEmbedding_mem S j, ?_, heq⟩
    exact fun h => hji (setLabelEmbedding_injective S h)
  · intro i _ j _ hij
    exact setLabelEmbedding_injective S hij
  · intro v hv
    obtain ⟨hvS, w, hwS, hwv, heq⟩ := (mem_repeatedVertices S f v).mp hv
    let i := S.equivFin ⟨v, hvS⟩
    let j := S.equivFin ⟨w, hwS⟩
    have hi : setLabelEmbedding S i = v := by simp [setLabelEmbedding, i]
    have hj : setLabelEmbedding S j = w := by simp [setLabelEmbedding, j]
    refine ⟨i, (mem_repeatedIndices (orderedSetLabels S f) i).mpr ⟨j, ?_, ?_⟩, hi⟩
    · intro h
      apply hwv
      rw [← hj, ← hi, h]
    · change f (setLabelEmbedding S j) = f (setLabelEmbedding S i)
      rw [hi, hj]
      exact heq

theorem repeatedVertices_card_le_twice_collisions {V A : Type*} (S : Finset V) (f : V → A) :
    (repeatedVertices S f).card ≤ 2 * (collisionIndices (orderedSetLabels S f)).card := by
  rw [repeatedVertices_card_eq_indices]
  exact repeatedIndices_card_le_twice_collisions _

end Erdos911
