import Erdos911.PolynomialDegreeBands
import Erdos911.DyadicThresholdDecomposition
import Erdos911.BandMassBudget

namespace Erdos911

/-- The high-left-degree band bound used by the reduction.
Its proof is supplied through the complete assembly in FullProof. -/
def HighDegreeBandStatement (A : ℕ) : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ q₀ : ℕ, ∀ q ≥ q₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∀ left right : Finset V, G.IsBipartiteWith (left : Set V) (right : Set V) →
      (∀ v ∈ G.support, (q : ℝ) / 65536 ≤ G.degree v) →
      (∀ v ∈ right, G.degree v ≤ 2 * q) →
      (∀ v ∈ left, v ∈ G.support → (q : ℝ) ^ A / 8 < G.degree v) →
      (M * q) * G.edgeSet.ncard ≤ (SimpleGraph.sizeRamsey G G : ℝ)

def MinimumDegreeRamseyStatement : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      0 < Fintype.card V → (∀ v, d ≤ G.degree v) →
        (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ)

/-- No maximum-degree hypothesis is needed once the high-left-degree
bands are controlled. The sum is over all active dyadic scales. -/
theorem minimum_degree_statement_of_high_bands (A : ℕ) (hA : 1 ≤ A)
    (hHigh : HighDegreeBandStatement A) : MinimumDegreeRamseyStatement := by
  intro M hM
  let M₁ := 128 * M
  have hM₁ : 1 ≤ M₁ := by dsimp only [M₁]; linarith
  obtain ⟨qL, hL⟩ := polynomial_degree_band_bound A M₁ hA hM₁
  obtain ⟨qH, hH⟩ := hHigh M₁ hM₁
  let Q := max 1 (max qL qH)
  refine ⟨2 * Q, ?_⟩
  intro d hd V _ _ G _ hV hmin
  classical
  have hdpos : 0 < d := by dsimp only [Q] at hd; omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hepos : (0 : ℝ) < G.edgeSet.ncard := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV
    have hv : 0 < G.degree v := hdpos.trans_le (hmin v)
    have he := hv.trans_le (G.degree_le_card_edgeFinset v)
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at he
    exact_mod_cast he
  let T := fun j : ℕ => ((2 : ℝ) ^ j) ^ A
  have hT : ∀ j, 0 ≤ T j := by intro j; positivity
  obtain ⟨left, right, L, H, hsub, hBip, hminL, hminH, hmaxL, hleftH, hrightH, hmass, hactive⟩ :=
    exists_dyadic_threshold_decomposition G T hT
  let N := Nat.log 2 G.maxDegree + 1
  let R : ℝ := SimpleGraph.sizeRamsey G G
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hQ (j : Fin N) (hj : d < 2 * 2 ^ j.val) : Q ≤ 2 ^ j.val := by omega
  have hpiece (j : Fin N) (hj : d < 2 * 2 ^ j.val) :
      (M₁ * (2 : ℝ) ^ j.val) * ((L j).edgeSet.ncard + (H j).edgeSet.ncard : ℝ) ≤ 2 * R := by
    have hLq : qL ≤ 2 ^ j.val := (le_max_left _ _).trans ((le_max_right _ _).trans (hQ j hj))
    have hHq : qH ≤ 2 ^ j.val := (le_max_right _ _).trans ((le_max_right _ _).trans (hQ j hj))
    have hl := hL (2 ^ j.val) hLq V (L j)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hminL j)
      (by simpa only [T, Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hmaxL j)
    have hh := hH (2 ^ j.val) hHq V (H j) left right (hBip j).2
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hminH j)
      (by simpa only [SimpleGraph.ncard_neighborSet] using hrightH j)
      (by simpa only [T, Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hleftH j)
    have hmonoL : (SimpleGraph.sizeRamsey (L j) (L j) : ℝ) ≤ R := by
      dsimp only [R]
      exact_mod_cast sizeRamsey_mono ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).1⟩
        ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).1⟩
    have hmonoH : (SimpleGraph.sizeRamsey (H j) (H j) : ℝ) ≤ R := by
      dsimp only [R]
      exact_mod_cast sizeRamsey_mono ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).2⟩
        ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).2⟩
    push_cast at hl hh
    nlinarith only [hl, hh, hmonoL, hmonoH]
  have hsum : M₁ * (∑ j : Fin N, ((L j).edgeSet.ncard + (H j).edgeSet.ncard : ℝ)) ≤
      (2 * R) * ∑ j : Fin N, if d < 2 * 2 ^ j.val then 1 / (2 : ℝ) ^ j.val else 0 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : d < 2 * 2 ^ j.val
    · rw [ite_eq_left hj, mul_one_div]
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ j.val)).mpr
      nlinarith only [hpiece j hj]
    · rw [ite_eq_right hj, mul_zero]
      have hz : (L j).edgeSet.ncard + (H j).edgeSet.ncard = 0 := by
        by_contra hnot
        exact hj (hactive j d hmin (Nat.pos_of_ne_zero hnot))
      have hzR : ((L j).edgeSet.ncard + (H j).edgeSet.ncard : ℝ) = 0 := by exact_mod_cast hz
      rw [hzR, mul_zero]
  have hbound := mul_le_mul_of_nonneg_left (reciprocal_active_band_budget d N hdpos)
    (show 0 ≤ 2 * R by positivity)
  have hmass' := mul_le_mul_of_nonneg_left hmass (show 0 ≤ M₁ by linarith)
  have hcombined : M₁ * (21 / 128 : ℝ) * G.edgeSet.ncard ≤ (2 * R) * (4 / d) := by
    nlinarith only [hmass', hsum, hbound]
  have hscaled := mul_le_mul_of_nonneg_right hcombined hdR.le
  have hcancel : ((2 * R) * (4 / d)) * d = 8 * R := by
    field_simp [hdR.ne']
    ring
  rw [hcancel] at hscaled
  dsimp only [M₁] at hscaled
  by_contra hnot
  have hcheap : R ≤ (M * d) * G.edgeSet.ncard := le_of_not_gt hnot
  have hpositive : 0 < (M * d) * G.edgeSet.ncard := mul_pos (mul_pos (by linarith) hdR) hepos
  nlinarith only [hscaled, hcheap, hpositive]

end Erdos911
