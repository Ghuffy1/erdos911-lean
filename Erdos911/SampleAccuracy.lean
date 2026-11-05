import Erdos911.SampleAlteration

open MeasureTheory

namespace Erdos911

theorem cubeProbability_union_le {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (A B : Set (Fin n → Bool)) :
    cubeProbability p (A ∪ B) ≤ cubeProbability p A + cubeProbability p B := by
  simp only [cubeProbability_eq_measureReal p hp₀ hp₁]
  exact measureReal_union_le A B

theorem cubeProbability_empty {n : ℕ} (p : Fin n → ℝ) :
    cubeProbability p ∅ = 0 := by
  simp [cubeProbability, cubeMean_const]

/-- Additive accuracy for a numerator and its positive denominator gives
accuracy for their ratio. The true numerator is r times the true denominator. -/
theorem ratio_accuracy (a b z r ε : ℝ) (hz : 0 < z)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (ha : |a - z * r| ≤ ε * z / 4) (hb : |b - z| ≤ ε * z / 4) :
    0 < b ∧ |a / b - r| ≤ ε := by
  let δ := ε * z / 4
  have hδ₀ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ z / 4 := by
    have h := mul_le_mul_of_nonneg_right hε₁ hz.le
    dsimp [δ]
    linarith
  have ha' : -δ ≤ a - z * r ∧ a - z * r ≤ δ := abs_le.mp ha
  have hb' : -δ ≤ b - z ∧ b - z ≤ δ := abs_le.mp hb
  have hbLower : 3 * z / 4 ≤ b := by linarith
  have hbpos : 0 < b := by linarith
  have hrδ : r * δ ≤ δ := by
    nlinarith [mul_le_mul_of_nonneg_right hr₁ hδ₀]
  have hprodLower := mul_le_mul_of_nonneg_left hb'.1 hr₀
  have hprodUpper := mul_le_mul_of_nonneg_left hb'.2 hr₀
  have hnum : |a - r * b| ≤ 2 * δ := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hbudget : 2 * δ ≤ ε * b := by
    have h := mul_le_mul_of_nonneg_left hbLower hε₀
    dsimp [δ]
    nlinarith [mul_nonneg hε₀ hz.le]
  refine ⟨hbpos, ?_⟩
  rw [show a / b - r = (a - r * b) / b by field_simp,
    abs_div, abs_of_pos hbpos]
  exact (div_le_iff₀ hbpos).mpr (hnum.trans hbudget)

/-- Simultaneous sampling accuracy for a subset and its ambient neighborhood.
The denominator is required to be nonzero even when the true fraction is zero. -/
theorem sample_fraction_accuracy {n : ℕ} (U V : Finset (Fin n)) (hVU : V ⊆ U)
    (hU : 0 < U.card) (p ε : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    cubeProbability (fun _ => p)
      {ω | sampleCount U ω ≤ 0 ∨
        ε < |sampleCount V ω / sampleCount U ω - (V.card : ℝ) / U.card|} ≤
      4 * Real.exp (-(ε ^ 2 * (p * U.card)) / 128) := by
  classical
  let μ : ℝ := p * U.card
  let A : Set (Fin n → Bool) := {ω | ε * μ / 4 ≤ |sampleCount V ω - p * V.card|}
  let B : Set (Fin n → Bool) := {ω | ε * μ / 4 ≤ |sampleCount U ω - μ|}
  have hsumV : (∑ j : V, p) = p * V.card := by simp [mul_comm]
  have hsumU : (∑ j : U, p) = μ := by simp [μ, mul_comm]
  have hmeanV : (∑ j : V, p) ≤ μ := by
    rw [hsumV]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hVU) hp₀.le
  have hA := sample_count_two_sided (fun _ => p) V μ (ε / 4)
    (fun _ => hp₀.le) (fun _ => hp₁) hmeanV (by positivity) (by linarith)
  have hB := sample_count_two_sided (fun _ => p) U μ (ε / 4)
    (fun _ => hp₀.le) (fun _ => hp₁) hsumU.le (by positivity) (by linarith)
  have hδ : (ε / 4) * μ = ε * μ / 4 := by ring
  have he : -((ε / 4) ^ 2 * μ) / 8 = -(ε ^ 2 * μ) / 128 := by ring
  rw [hsumV, hδ, he] at hA
  rw [hsumU, hδ, he] at hB
  have hsubset : {ω | sampleCount U ω ≤ 0 ∨
      ε < |sampleCount V ω / sampleCount U ω - (V.card : ℝ) / U.card|} ⊆ A ∪ B := by
    intro ω hbad
    by_contra hout
    have hnotA : ω ∉ A := fun h => hout (Or.inl h)
    have hnotB : ω ∉ B := fun h => hout (Or.inr h)
    have hnum : |sampleCount V ω - p * V.card| ≤ ε * μ / 4 :=
      (lt_of_not_ge hnotA).le
    have hden : |sampleCount U ω - μ| ≤ ε * μ / 4 := (lt_of_not_ge hnotB).le
    have hUreal : (0 : ℝ) < U.card := by exact_mod_cast hU
    have hr₀ : (0 : ℝ) ≤ (V.card : ℝ) / U.card := by positivity
    have hr₁ : (V.card : ℝ) / U.card ≤ 1 :=
      (div_le_one hUreal).mpr (by exact_mod_cast Finset.card_le_card hVU)
    have hidentity : μ * ((V.card : ℝ) / U.card) = p * V.card := by
      dsimp [μ]
      field_simp
    have hgood := ratio_accuracy (sampleCount V ω) (sampleCount U ω) μ
      ((V.card : ℝ) / U.card) ε (by dsimp [μ]; positivity) hr₀ hr₁ hε₀ hε₁
      (by simpa only [hidentity] using hnum) hden
    exact hbad.elim (not_le_of_gt hgood.1) (not_lt_of_ge hgood.2)
  rw [cubeProbability_eq_measureReal (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)]
  calc
    (bernoulliCubeMeasure (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)).real
        {ω | sampleCount U ω ≤ 0 ∨
          ε < |sampleCount V ω / sampleCount U ω - (V.card : ℝ) / U.card|} ≤
        (bernoulliCubeMeasure (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)).real (A ∪ B) :=
      measureReal_mono hsubset
    _ ≤ (bernoulliCubeMeasure (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)).real A +
        (bernoulliCubeMeasure (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)).real B :=
      measureReal_union_le A B
    _ ≤ 4 * Real.exp (-(ε ^ 2 * (p * U.card)) / 128) := by
      dsimp [A, B, μ] at hA hB ⊢
      linarith

theorem sampleCount_pos_iff {n : ℕ} (U : Finset (Fin n)) (ω : Fin n → Bool) :
    0 < sampleCount U ω ↔ ∃ j ∈ U, ω j = true := by
  rw [sampleCount_eq_card]
  simp only [Nat.cast_pos, Finset.card_pos, Finset.Nonempty, Finset.mem_filter]

theorem sampleCount_nonpos_iff {n : ℕ} (U : Finset (Fin n)) (ω : Fin n → Bool) :
    sampleCount U ω ≤ 0 ↔ ∀ j ∈ U, ω j = false := by
  rw [← not_lt, sampleCount_pos_iff]
  simp

def samplingFailure {n : ℕ} {ι : Type*} (U : Finset (Fin n))
    (V : ι → Finset (Fin n)) (C : Finset ι) (ε : ℝ) : Set (Fin n → Bool) :=
  {ω | sampleCount U ω ≤ 0 ∨
    ∃ i ∈ C, ε < |sampleCount (V i) ω / sampleCount U ω - ((V i).card : ℝ) / U.card|}

/-- Union bound for the simultaneous candidate-fraction tests at one role. -/
theorem samplingFailure_probability {n : ℕ} {ι : Type*}
    (U : Finset (Fin n)) (V : ι → Finset (Fin n)) (C : Finset ι)
    (hV : ∀ i ∈ C, V i ⊆ U) (hU : 0 < U.card)
    (p ε : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    cubeProbability (fun _ => p) (samplingFailure U V C ε) ≤
      (4 * C.card + 1) * Real.exp (-(ε ^ 2 * (p * U.card)) / 128) := by
  classical
  let μ := bernoulliCubeMeasure (fun _ : Fin n => p) (fun _ => hp₀.le) (fun _ => hp₁)
  let B := fun i => {ω : Fin n → Bool |
    ε < |sampleCount (V i) ω / sampleCount U ω - ((V i).card : ℝ) / U.card|}
  let E := Real.exp (-(ε ^ 2 * (p * U.card)) / 128)
  have hnone : μ.real {ω | sampleCount U ω ≤ 0} ≤ E := by
    rw [← cubeProbability_eq_measureReal (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)]
    have heq : {ω : Fin n → Bool | sampleCount U ω ≤ 0} =
        {ω | ∀ j ∈ U, ω j = false} := by
      ext ω
      exact sampleCount_nonpos_iff U ω
    rw [heq]
    apply (empty_sample_probability_le p U hp₀.le hp₁).trans
    apply Real.exp_le_exp.mpr
    have hεsq : ε ^ 2 ≤ 1 := by nlinarith
    have hmass : 0 ≤ p * U.card := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hεsq hmass]
  have hB : ∀ i ∈ C, μ.real (B i) ≤ 4 * E := by
    intro i hi
    apply le_trans (b := μ.real {ω | sampleCount U ω ≤ 0 ∨
      ε < |sampleCount (V i) ω / sampleCount U ω - ((V i).card : ℝ) / U.card|})
    · exact measureReal_mono (fun _ h => Or.inr h)
    · rw [← cubeProbability_eq_measureReal (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)]
      exact sample_fraction_accuracy U (V i) (hV i hi) hU p ε hp₀ hp₁ hε₀ hε₁
  have hevent : samplingFailure U V C ε = {ω | sampleCount U ω ≤ 0} ∪ ⋃ i ∈ C, B i := by
    ext ω
    simp only [samplingFailure, B, Set.mem_union, Set.mem_ofPred_eq,
      Set.mem_iUnion, exists_prop]
  rw [cubeProbability_eq_measureReal (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁), hevent]
  calc
    μ.real ({ω | sampleCount U ω ≤ 0} ∪ ⋃ i ∈ C, B i) ≤
        μ.real {ω | sampleCount U ω ≤ 0} + μ.real (⋃ i ∈ C, B i) := measureReal_union_le _ _
    _ ≤ E + ∑ i ∈ C, μ.real (B i) :=
      add_le_add hnone (measureReal_biUnion_finset_le C B)
    _ ≤ E + ∑ _i ∈ C, 4 * E := add_le_add le_rfl (Finset.sum_le_sum hB)
    _ = (4 * C.card + 1) * E := by simp; ring

end Erdos911
