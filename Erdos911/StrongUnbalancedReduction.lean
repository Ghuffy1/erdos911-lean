import Erdos911.UnbalancedPowerWindow
import Erdos911.UnbalancedMedianNormalization
import Erdos911.FinalDensityReduction

namespace Erdos911

/-- The strongly unbalanced Ramsey statement used by the reduction. It allows
arbitrary left degree scale P and a degree ratio at most d^4.
This definition does not assert the obligation. -/
def StronglyUnbalancedRamseyStatement : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (L R : Type) [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
      (S : R → Finset L) (P : ℝ),
      0 < Fintype.card (L ⊕ R) → (d : ℝ) ^ 200 ≤ P →
      (∀ y, (incidenceGraph S).degree (Sum.inr y) = d) →
      (∀ x, P ≤ (incidenceGraph S).degree (Sum.inl x)) →
      (∀ x, ((incidenceGraph S).degree (Sum.inl x) : ℝ) ≤ (d : ℝ) ^ 4 * P) →
      (M * d) * (incidenceGraph S).edgeSet.ncard <
        (SimpleGraph.sizeRamsey (incidenceGraph S) (incidenceGraph S) : ℝ)

/-- The high-degree branch reduces to strongly unbalanced targets with
one fixed degree-ratio exponent. No iterative band regularization is used. -/
theorem high_bands_of_strongly_unbalanced (h : StronglyUnbalancedRamseyStatement) :
    HighDegreeBandStatement 210 := by
  intro M hM
  let M' := 140737488355328 * M
  have hM' : 1 ≤ M' := by dsimp only [M']; linarith
  obtain ⟨d₀, hd₀⟩ := h M' hM'
  obtain ⟨Q, hQ⟩ := unbalanced_median_normalization
  refine ⟨max Q (max (2 ^ 64) (max (1048576 * d₀) (Nat.ceil M))), ?_⟩
  intro q hq V _ _ G _ left right hB hmin hright hleft
  classical
  have hqQ : Q ≤ q := (le_max_left _ _).trans hq
  have hq64 : 2 ^ 64 ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have hqd₀ : 1048576 * d₀ ≤ q := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hq))
  have hqM : Nat.ceil M ≤ q := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hq))
  have hMq : M ≤ (q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hqM)
  have hq8 : (8 : ℝ) ≤ q := by exact_mod_cast (show 8 ≤ q by norm_num at hq64; omega)
  have hq1 : 1 ≤ q := by norm_num at hq64; omega
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hΛ : 1 ≤ M * q := one_le_mul_of_one_le_of_one_le hM hqR
  have hΛq : M * q ≤ (q : ℝ) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hMq (Nat.cast_nonneg (α := ℝ) q)
    nlinarith only [hm]
  by_cases he : 0 < G.edgeSet.ncard
  · by_contra hnot
    have hcheap : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * q) * G.edgeSet.ncard :=
      (lt_of_not_ge hnot).le
    have hleft' (v : V) (hv : v ∈ left) (hs : v ∈ G.support) : q ^ 209 ≤ G.degree v := by
      have hm := mul_le_mul_of_nonneg_right hq8 (pow_nonneg (Nat.cast_nonneg (α := ℝ) q) 209)
      have hp : (q : ℝ) ^ 209 ≤ (q : ℝ) ^ 210 / 8 := by
        rw [show (q : ℝ) ^ 210 = (q : ℝ) ^ 209 * q by rw [show 210 = 209 + 1 from rfl, pow_succ]]
        nlinarith only [hm]
      exact_mod_cast hp.trans (hleft v hv hs).le
    have hpower : q ^ 3 ≤ q ^ 209 := Nat.pow_le_pow_right hq1 (by omega)
    obtain ⟨p, H, S, hp, _, hSG, hcard, hSright, hSleft, hSmax, hmass⟩ :=
      hQ q hqQ (q ^ 209) hpower V G left right hB he hmin hleft' hright (M * q) hΛ hΛq hcheap
    let P := (p : ℝ) / 134217728
    obtain ⟨_, hP, hcap⟩ := unbalanced_power_window q p (M * q) hq64 hp (by positivity) hΛq
    have htd₀ : d₀ ≤ unbalancedRightDegree q := by unfold unbalancedRightDegree; omega
    have hS := hd₀ (unbalancedRightDegree q) htd₀ _ _ S P hcard hP hSright hSleft
      (fun x => (hSmax (Sum.inl x)).trans hcap)
    have hqt : (q : ℝ) ≤ 2097152 * unbalancedRightDegree q := by
      exact_mod_cast (show q ≤ 2097152 * unbalancedRightDegree q by unfold unbalancedRightDegree; norm_num at hq64; omega)
    have hcoef : (M * q) * 67108864 ≤ M' * unbalancedRightDegree q := by
      have hm := mul_le_mul_of_nonneg_left hqt (show 0 ≤ 67108864 * M by positivity)
      dsimp only [M']
      nlinarith only [hm]
    have hbudget : (M * q) * G.edgeSet.ncard ≤
        (M' * unbalancedRightDegree q) * (incidenceGraph S).edgeSet.ncard := by
      have h₁ := mul_le_mul_of_nonneg_left hmass (show 0 ≤ M * (q : ℝ) by positivity)
      have h₂ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (α := ℝ) (incidenceGraph S).edgeSet.ncard)
      nlinarith only [h₁, h₂]
    have hmono : (SimpleGraph.sizeRamsey (incidenceGraph S) (incidenceGraph S) : ℝ) ≤
        SimpleGraph.sizeRamsey G G := by exact_mod_cast sizeRamsey_mono hSG hSG
    exact (not_lt_of_ge hcheap) (hbudget.trans_lt (hS.trans_le hmono))
  · have hz : G.edgeSet.ncard = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero]
    positivity

/-- The exact conclusion from the strongly unbalanced statement.
The required statement is proved in the full assembly. -/
theorem exact_of_strongly_unbalanced (h : StronglyUnbalancedRamseyStatement) : ExactStatement :=
  exact_of_high_degree_bands 210 (by norm_num) (high_bands_of_strongly_unbalanced h)

end Erdos911
