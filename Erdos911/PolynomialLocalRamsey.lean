import Erdos911.BandRamsey
import Erdos911.BandScaleTransport
import Erdos911.BandMassBudget
import Erdos911.DyadicThresholdDecomposition

namespace Erdos911

/-- The two branch theorems and the geometric band budget imply the
uniform superlinear bound for polynomial maximum degree and local density.
No regularity or bipartiteness is assumed on the original target. -/
theorem polynomial_local_size_ramsey_lower_bound (B : ℕ) (M C : ℝ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], 0 < Fintype.card V →
      (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ d ^ B) →
      (∀ S : Finset V, S.card ≤ d ^ (B + 1) →
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  let M₁ : ℝ := 2199023255552 * M
  have hM₁ : 1 ≤ M₁ := by dsimp only [M₁]; linarith
  obtain ⟨qL, hL⟩ := low_band_ramsey_bound M₁ (2 * C) hM₁ (by positivity)
  obtain ⟨qH, hH⟩ := high_band_ramsey_bound B M₁ (2 * C) hM₁ (by positivity)
  let Q := max qL (max qH (max 131072 (65536 * 262144)))
  refine ⟨max 2 (2 * Q), ?_⟩
  intro d hd V _ _ G _ hV hmin hmax hlocal
  classical
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdQ : 2 * Q ≤ d := (le_max_right _ _).trans hd
  let : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨v⟩ := ‹Nonempty V›
  have hDpos : 0 < G.maxDegree := by
    have h := (hmin v).trans (G.degree_le_maxDegree v)
    omega
  have hepos : (0 : ℝ) < G.edgeSet.ncard := by
    have hdegree : 0 < G.degree v := by have h := hmin v; omega
    have h := hdegree.trans_le (G.degree_le_card_edgeFinset v)
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
    exact_mod_cast h
  have hT (j : ℕ) : 0 ≤ bandLeftThreshold (2 ^ j) := by
    unfold bandLeftThreshold
    positivity
  obtain ⟨left, right, L, H, hsub, hBip, hminL, hminH, hmaxL, hleftH, hrightH, hmass, hactive⟩ :=
    exists_dyadic_threshold_decomposition G (fun j => bandLeftThreshold (2 ^ j)) hT
  let N := Nat.log 2 G.maxDegree + 1
  have hQ (j : Fin N) (hj : d < 2 * 2 ^ j.val) : Q ≤ 2 ^ j.val := by omega
  have hqlarge (j : Fin N) (hj : d < 2 * 2 ^ j.val) : 131072 ≤ 2 ^ j.val :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hQ j hj)))
  have hdlarge (j : Fin N) (hj : d < 2 * 2 ^ j.val) : 262144 ≤ bandDegree (2 ^ j.val) := by
    have h := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hQ j hj)))
    unfold bandDegree
    omega
  have hupper (j : Fin N) : 2 ^ j.val ≤ d ^ B :=
    (dyadic_band_upper_bound G hDpos j).trans (G.maxDegree_le_of_forall_degree_le _ hmax)
  have hlocalL (j : Fin N) (hj : d < 2 * 2 ^ j.val) :=
    band_copy_local_density G (L j) (SimpleGraph.Copy.ofLE _ _ (hsub j).1)
      B d (2 ^ j.val) C hC hd2 (hqlarge j hj) hj (hdlarge j hj) (hupper j) hlocal
  have hlocalH (j : Fin N) (hj : d < 2 * 2 ^ j.val) :=
    band_copy_local_density G (H j) (SimpleGraph.Copy.ofLE _ _ (hsub j).2)
      B d (2 ^ j.val) C hC hd2 (hqlarge j hj) hj (hdlarge j hj) (hupper j) hlocal
  let R : ℝ := SimpleGraph.sizeRamsey G G
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hpiece (j : Fin N) (hj : d < 2 * 2 ^ j.val) :
      (M₁ * bandDegree (2 ^ j.val)) *
        ((L j).edgeSet.ncard + (H j).edgeSet.ncard : ℝ) ≤ 262145 * R := by
    have hLj := hL (2 ^ j.val) ((le_max_left _ _).trans (hQ j hj)) V (L j)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hminL j)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hmaxL j)
      (hlocalL j hj)
    have hHj := hH (2 ^ j.val)
      ((le_max_left _ _).trans ((le_max_right _ _).trans (hQ j hj))) V (H j) left right
      (hBip j).2
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat, SimpleGraph.ncard_neighborSet] using hminH j)
      (fun w => ((SimpleGraph.Copy.ofLE _ _ (hsub j).2).degree_le w).trans
        ((hmax w).trans (Nat.pow_le_pow_left (by omega : d ≤ 2 * 2 ^ j.val) B)))
      (by simpa only [SimpleGraph.ncard_neighborSet] using hrightH j)
      (by simpa only [SimpleGraph.ncard_neighborSet] using hleftH j)
      (hlocalH j hj)
    have hmonoL : (SimpleGraph.sizeRamsey (L j) (L j) : ℝ) ≤ R := by
      dsimp only [R]
      exact_mod_cast sizeRamsey_mono ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).1⟩
        ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).1⟩
    have hmonoH : (SimpleGraph.sizeRamsey (H j) (H j) : ℝ) ≤ R := by
      dsimp only [R]
      exact_mod_cast sizeRamsey_mono ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).2⟩
        ⟨SimpleGraph.Copy.ofLE _ _ (hsub j).2⟩
    nlinarith only [hLj, hHj, hmonoL, hmonoH]
  have hsum : M₁ * (∑ j : Fin N, ((L j).edgeSet.ncard + (H j).edgeSet.ncard : ℝ)) ≤
      (262145 * R) * ∑ j : Fin N, if d < 2 * 2 ^ j.val then
        1 / (bandDegree (2 ^ j.val) : ℝ) else 0 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : d < 2 * 2 ^ j.val
    · rw [ite_eq_left hj, mul_one_div]
      have hpositive : (0 : ℝ) < bandDegree (2 ^ j.val) := by
        exact_mod_cast (bandDegree_bounds (2 ^ j.val) (hqlarge j hj)).1
      apply (le_div_iff₀ hpositive).mpr
      nlinarith only [hpiece j hj]
    · rw [ite_eq_right hj, mul_zero]
      have hz : (L j).edgeSet.ncard + (H j).edgeSet.ncard = 0 := by
        by_contra hnot
        exact hj (hactive j d hmin (Nat.pos_of_ne_zero hnot))
      have hzR : ((L j).edgeSet.ncard + (H j).edgeSet.ncard : ℝ) = 0 := by exact_mod_cast hz
      rw [hzR, mul_zero]
  have hbudget := reciprocal_normalized_band_budget d N (by omega) hqlarge
  have hbound := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ 262145 * R from mul_nonneg (by norm_num) hR)
  have hmass' := mul_le_mul_of_nonneg_left hmass (show 0 ≤ M₁ by linarith)
  by_contra hnot
  have hcheap : R ≤ (M * d) * G.edgeSet.ncard := le_of_not_gt hnot
  have hcombined : M₁ * (21 / 128 : ℝ) * G.edgeSet.ncard ≤ (262145 * R) * (524288 / d) := by
    nlinarith only [hmass', hsum, hbound]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hcombined' := mul_le_mul_of_nonneg_right hcombined hdpos.le
  have hdcancel : ((262145 * R) * (524288 / d)) * d = 137439477760 * R := by
    field_simp [hdpos.ne']
    ring
  rw [hdcancel] at hcombined'
  dsimp only [M₁] at hcombined'
  have hpositive : 0 < (M * d) * G.edgeSet.ncard := mul_pos (mul_pos (by linarith) hdpos) hepos
  nlinarith only [hcombined', hcheap, hpositive]

end Erdos911
