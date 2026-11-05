import Erdos911.BiasedBits
import Erdos911.FiniteEventMarkov

open MeasureTheory

namespace Erdos911

noncomputable def dictionaryRowCoordinates {L C : Type*} [DecidableEq L] [DecidableEq C]
    (S : Finset L) (j : C) : Finset (L × C) := S.image (fun x => (x, j))

def dictionaryUniformRow {L C : Type*} (S : Finset L) (j : C) : Set ((L × C) → Bool) :=
  {ω | ∃ b : Bool, ∀ x ∈ S, ω (x, j) = b}

theorem dictionaryRowCoordinates_card {L C : Type*} [DecidableEq L] [DecidableEq C]
    (S : Finset L) (j : C) : (dictionaryRowCoordinates S j).card = S.card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem dictionaryRowCoordinates_disjoint {L C : Type*} [DecidableEq L] [DecidableEq C]
    (S T : Finset L) (j k : C) (hjk : j ≠ k) :
    Disjoint (dictionaryRowCoordinates S j) (dictionaryRowCoordinates T k) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp he
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hf
  exact hjk (congrArg Prod.snd (hx.trans hy.symm))

theorem dictionaryUniformRow_depends {L C : Type*} [DecidableEq L] [DecidableEq C]
    (S : Finset L) (j : C) :
    DependsOnlyOn (dictionaryUniformRow S j) (dictionaryRowCoordinates S j) := by
  intro ω ω' heq hω
  obtain ⟨b, hb⟩ := hω
  refine ⟨b, ?_⟩
  intro x hx
  rw [← heq (x, j) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
  exact hb x hx

/-- A row is uniform in one coordinate only if all its independent
label bits take one of the two constant values. -/
theorem dictionaryUniformRow_probability {L C : Type*}
    [Fintype L] [DecidableEq L] [Fintype C] [DecidableEq C]
    (S : Finset L) (j : C) :
    (bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)).real
      (dictionaryUniformRow S j) ≤ 2 * (1 / 2 : ℝ) ^ S.card := by
  classical
  let μ := bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)
  let A : Bool → Set ((L × C) → Bool) := fun b => fixedBits (dictionaryRowCoordinates S j) b
  have hcover : dictionaryUniformRow S j ⊆ ⋃ b, A b := by
    rintro ω ⟨b, hb⟩
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact hb x hx
  have hprob (b : Bool) : μ.real (A b) = (1 / 2 : ℝ) ^ S.card := by
    rw [bitProductMeasure_fixedBits, dictionaryRowCoordinates_card]
    cases b <;> norm_num [bernoulliWeight]
  have hsum : (∑ b : Bool, μ.real (A b)) = 2 * (1 / 2 : ℝ) ^ S.card := by simp only [hprob]; simp
  exact ((measureReal_mono hcover).trans (measureReal_iUnion_fintype_le A)).trans_eq hsum

theorem dictionaryUniformRow_probability_of_minimum {L C : Type*}
    [Fintype L] [DecidableEq L] [Fintype C] [DecidableEq C]
    (S : Finset L) (j : C) (s : ℕ) (hs : s ≤ S.card) :
    (bitProductMeasure (L × C) (1 / 2) (by norm_num) (by norm_num)).real
      (dictionaryUniformRow S j) ≤ 2 * (1 / 2 : ℝ) ^ s := by
  apply (dictionaryUniformRow_probability S j).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) hs)
    (by norm_num)

end Erdos911
