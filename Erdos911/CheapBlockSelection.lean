import Erdos911.SurvivingPatternRows
import Erdos911.TargetTruncationMass
import Erdos911.CheapImageBounds
import Erdos911.SmallPatternCount

namespace Erdos911

noncomputable def cheapBlockSurvivingRows {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [Fintype V]
    (N : R → Finset A) (K : SimpleGraph V) [DecidableRel K.Adj]
    (g : A ⊕ R → V) (q : ℕ) : Finset R :=
  survivingPatternRows
    (substantialTargetRows (targetTruncatedRows N (dictionaryLowDegree q)) (dictionaryRowMinimum q))
    (targetTruncatedRows N (dictionaryLowDegree q))
    (fun y => K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q)
    (Fintype.card R) (dictionaryPatternCount q)

/-- Every cheap image of one large-right target block has at least
three eighths of its right vertices in the surviving low patterns. -/
theorem cheap_block_surviving_rows_large {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V]
    (N : R → Finset A) (K : SimpleGraph V) [DecidableRel K.Adj]
    (g : A ⊕ R → V) (q : ℕ) (hq : 0 < q)
    (hrow : ∀ y, (N y).card = q) (hA : Fintype.card A ≤ dictionaryLeftSize q)
    (hR : 128 * q ^ 69 ≤ Fintype.card R)
    (hcheap : (∑ v : A ⊕ R, K.degree (g v)) ≤ dictionaryDegreeCharge q * Fintype.card R) :
    3 * Fintype.card R ≤ 8 * (cheapBlockSurvivingRows N K g q).card := by
  classical
  let T := targetTruncatedRows N (dictionaryLowDegree q)
  let B := substantialTargetRows T (dictionaryRowMinimum q)
  let Low := fun y => K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q
  have hΓ : 0 < dictionaryDegreeCharge q := by unfold dictionaryDegreeCharge; positivity
  have hM : 0 < dictionaryPatternCount q := by unfold dictionaryPatternCount; positivity
  have hlarge : 16 * Fintype.card A * dictionaryLowDegree q ≤ q * Fintype.card R := by
    calc
      _ ≤ 16 * dictionaryLeftSize q * dictionaryLowDegree q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA)
      _ = q * (128 * q ^ 69) := by unfold dictionaryLeftSize dictionaryLowDegree dictionaryDegreeCharge; ring
      _ ≤ q * Fintype.card R := Nat.mul_le_mul_left q hR
  have hB : 7 * Fintype.card R ≤ 8 * B.card := substantial_target_rows_large N q _ hq hrow hlarge
  have hpatterns : (B.image T).card ≤ dictionaryPatternCount q := by
    apply row_pattern_image_card_bound T B q (dictionaryLeftSize q)
    · intro y _
      exact (Finset.card_le_card (targetTruncatedRows_subset N _ y)).trans (hrow y).le
    · exact hA
  have hh := (cheap_image_degree_bounds K g (dictionaryDegreeCharge q) hΓ hcheap).2
  have hhigh : 8 * (B.filter (fun y => ¬Low y)).card ≤ Fintype.card R := by
    have hsub : B.filter (fun y => ¬Low y) ⊆ (Finset.univ : Finset R).filter
        (fun y => 8 * dictionaryDegreeCharge q < K.degree (g (Sum.inr y))) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have hn := (Finset.mem_filter.mp hy).2
        change ¬K.degree (g (Sum.inr y)) ≤ 8 * dictionaryDegreeCharge q at hn
        omega⟩
    exact (Nat.mul_le_mul_left 8 (Finset.card_le_card hsub)).trans hh
  exact survivingPatternRows_card_bound B T Low (Fintype.card R) (dictionaryPatternCount q) hM hpatterns hB hhigh

end Erdos911
