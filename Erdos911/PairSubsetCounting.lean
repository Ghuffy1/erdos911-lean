import Erdos911.FinitePairing
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod

namespace Erdos911

noncomputable def pairWitnessSubsets {E : Type*} [DecidableEq E]
    (U : Finset E) (A : Finset (E × E)) (a j : ℕ) : Finset (Finset E) := by
  classical
  exact (U.powersetCard a).filter (fun F =>
    ∃ Q : Finset (E × E), IsPairPacking F Q ∧ Q ⊆ A ∧ Q.card = j)

theorem mem_pairWitnessSubsets {E : Type*} [DecidableEq E]
    (U : Finset E) (A : Finset (E × E)) (a j : ℕ) (F : Finset E) :
    F ∈ pairWitnessSubsets U A a j ↔ F ⊆ U ∧ F.card = a ∧
      ∃ Q : Finset (E × E), IsPairPacking F Q ∧ Q ⊆ A ∧ Q.card = j := by
  classical
  simp only [pairWitnessSubsets, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

/-- Encode an edge set by a chosen family of disjoint pairs and its
remaining edges. The encoding proves the repeated-pair binomial bound. -/
theorem pairWitnessSubsets_card_le {E : Type*} [DecidableEq E]
    (U : Finset E) (A : Finset (E × E)) (a j : ℕ) :
    (pairWitnessSubsets U A a j).card ≤ A.card.choose j * U.card.choose (a - 2 * j) := by
  classical
  let B := pairWitnessSubsets U A a j
  have hex : ∀ F : B, ∃ Q : Finset (E × E), IsPairPacking F.val Q ∧ Q ⊆ A ∧ Q.card = j := by
    intro F
    exact ((mem_pairWitnessSubsets U A a j F.val).mp F.property).2.2
  choose Q hpacking hQA hQcard using hex
  have hFsubset : ∀ F : B, F.val ⊆ U := by
    intro F
    exact ((mem_pairWitnessSubsets U A a j F.val).mp F.property).1
  have hFcard : ∀ F : B, F.val.card = a := by
    intro F
    exact ((mem_pairWitnessSubsets U A a j F.val).mp F.property).2.1
  have hremaining : ∀ F : B, (F.val \ pairVertexUnion (Q F)).card = a - 2 * j := by
    intro F
    rw [Finset.card_sdiff_of_subset (hpacking F).union_subset, hFcard F,
      (hpacking F).union_card, hQcard F]
  let encode : B → (A.powersetCard j) × (U.powersetCard (a - 2 * j)) := fun F =>
    (⟨Q F, Finset.mem_powersetCard.mpr ⟨hQA F, hQcard F⟩⟩,
      ⟨F.val \ pairVertexUnion (Q F),
        Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset.trans (hFsubset F), hremaining F⟩⟩)
  have hinj : Function.Injective encode := by
    intro F F' h
    have hQ : Q F = Q F' := congrArg (fun p => p.1.val) h
    have hR : F.val \ pairVertexUnion (Q F) = F'.val \ pairVertexUnion (Q F') :=
      congrArg (fun p => p.2.val) h
    apply Subtype.ext
    calc
      F.val = pairVertexUnion (Q F) ∪ (F.val \ pairVertexUnion (Q F)) :=
        (Finset.union_sdiff_of_subset (hpacking F).union_subset).symm
      _ = pairVertexUnion (Q F') ∪ (F'.val \ pairVertexUnion (Q F')) := by rw [hR, hQ]
      _ = F'.val := Finset.union_sdiff_of_subset (hpacking F').union_subset
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_prod, Fintype.card_coe, Finset.card_powersetCard] using hcard

end Erdos911
