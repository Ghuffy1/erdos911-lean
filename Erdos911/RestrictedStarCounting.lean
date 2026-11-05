import Erdos911.RestrictedStarEntropy
import Mathlib.Data.Fintype.BigOperators

namespace Erdos911

/-- Edge subsets reconstructed from a remainder and a prescribed number of
edges from each restricted star. Different descriptions may coincide. -/
noncomputable def restrictedStarSubsets {I E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] (U : Finset E) (A : I → Finset E) (b : ℕ) (t : I → ℕ) :
    Finset (Finset E) := by
  classical
  exact ((U.powersetCard b) ×ˢ Fintype.piFinset (fun i => (A i).powersetCard (t i))).image
    (fun data => data.1 ∪ Finset.univ.biUnion data.2)

theorem mem_restrictedStarSubsets {I E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] (U : Finset E) (A : I → Finset E) (b : ℕ) (t : I → ℕ) (F : Finset E) :
    F ∈ restrictedStarSubsets U A b t ↔
      ∃ (R : Finset E) (D : I → Finset E), R ⊆ U ∧ R.card = b ∧
        (∀ i, D i ⊆ A i ∧ (D i).card = t i) ∧ F = R ∪ Finset.univ.biUnion D := by
  classical
  constructor
  · intro hF
    obtain ⟨⟨R, D⟩, hdata, hF⟩ := Finset.mem_image.mp hF
    obtain ⟨hR, hD⟩ := Finset.mem_product.mp hdata
    obtain ⟨hRU, hRb⟩ := Finset.mem_powersetCard.mp hR
    exact ⟨R, D, hRU, hRb, fun i => Finset.mem_powersetCard.mp (Fintype.mem_piFinset.mp hD i),
      hF.symm⟩
  · rintro ⟨R, D, hRU, hRb, hD, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(R, D), Finset.mem_product.mpr ⟨Finset.mem_powersetCard.mpr ⟨hRU, hRb⟩, ?_⟩, rfl⟩
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_powersetCard.mpr (hD i))

theorem restrictedStarSubsets_card_le {I E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] (U : Finset E) (A : I → Finset E) (b : ℕ) (t : I → ℕ) :
    (restrictedStarSubsets U A b t).card ≤ U.card.choose b * ∏ i, (A i).card.choose (t i) := by
  classical
  calc
    (restrictedStarSubsets U A b t).card ≤
        ((U.powersetCard b) ×ˢ Fintype.piFinset (fun i => (A i).powersetCard (t i))).card :=
      Finset.card_image_le
    _ = _ := by rw [Finset.card_product, Finset.card_powersetCard, Fintype.card_piFinset]; simp

theorem restrictedStarSubsets_exp_bound {I E : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] (U : Finset E) (A : I → Finset E) (a b P : ℕ) (C t : I → ℕ)
    (hP : 0 < P) (hC : ∀ i, 0 < C i) (hk : 0 < Fintype.card I) (ha : 0 < a)
    (hU : U.card ≤ P * Fintype.card I) (hA : ∀ i, (A i).card ≤ C i)
    (hsplit : a = b + ∑ i, t i) :
    ((restrictedStarSubsets U A b t).card : ℝ) ≤
      Real.exp ((a : ℝ) * Real.log ((P * Fintype.card I : ℝ) / a) -
        (∑ i, (t i : ℝ) * Real.log ((P : ℝ) / C i)) + 2 * a) := by
  have hnat : (restrictedStarSubsets U A b t).card ≤
      (P * Fintype.card I).choose b * ∏ i, (C i).choose (t i) := by
    apply (restrictedStarSubsets_card_le U A b t).trans
    exact Nat.mul_le_mul (Nat.choose_le_choose b hU)
      (Finset.prod_le_prod (fun i _ => Nat.choose_le_choose (t i) (hA i)))
  have hreal : ((restrictedStarSubsets U A b t).card : ℝ) ≤
      ((P * Fintype.card I).choose b : ℝ) * ∏ i, ((C i).choose (t i) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans (restricted_star_choose_product_bound P a b C t hP hC hk ha hsplit)

end Erdos911
