import Erdos911.ForestErrorBounds
import Erdos911.PolynomialEntropyThreshold

open Filter

namespace Erdos911

theorem linear_host_forest_error {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph W) [DecidableRel K.Adj]
    (A d : ℕ) (M : ℝ) (hd : 1 ≤ d) (hM : 1 ≤ M) (hMd : M ≤ d)
    (hmin : ∀ v, d ≤ G.degree v) (hhost : 0 < K.edgeFinset.card)
    (hbudget : (K.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard)
    (herror : polynomialEntropyError 0 (A + 4) d ≤ 1) :
    forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent) K.edgeFinset.card (d ^ A) ≤
      G.edgeSet.ncard := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log d := Real.log_nonneg hdreal
  have hMpos : 0 < M := by linarith
  have hΛ : 1 ≤ M * d := by nlinarith
  have hdegree : 1 ≤ d ^ A := Nat.one_le_pow A d hd
  have h := graph_forest_error_bound G K d (d ^ A) hd hdegree hmin hhost (M * d) hΛ hbudget
  have hlogM : Real.log M ≤ Real.log d := Real.log_le_log hMpos hMd
  have hlogΛ : Real.log (M * d * d) ≤ 3 * Real.log d := by
    rw [Real.log_mul (mul_pos hMpos hdpos).ne' hdpos.ne', Real.log_mul hMpos.ne' hdpos.ne']
    linarith
  have hlogD : Real.log ((d ^ A : ℕ) : ℝ) = (A : ℝ) * Real.log d := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlogD] at h
  have hnonneg : (0 : ℝ) ≤ G.edgeSet.ncard := Nat.cast_nonneg _
  have hcoefficient : (2 * G.edgeSet.ncard / (d : ℝ)) *
      (2 * (Real.log (M * d * d) + 1) + A * Real.log d) ≤
      polynomialEntropyError 0 (A + 4) d * G.edgeSet.ncard := by
    calc
      _ ≤ (2 * G.edgeSet.ncard / (d : ℝ)) * (2 * (3 * Real.log d + 1) + A * Real.log d) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ polynomialEntropyError 0 (A + 4) d * G.edgeSet.ncard := by
        have hdiff : 0 ≤ (G.edgeSet.ncard : ℝ) * (Real.log d + 2) / d := by positivity
        have heq : polynomialEntropyError 0 (A + 4) d * G.edgeSet.ncard -
            (2 * G.edgeSet.ncard / (d : ℝ)) * (2 * (3 * Real.log d + 1) + A * Real.log d) =
            (G.edgeSet.ncard : ℝ) * (Real.log d + 2) / d := by
          unfold polynomialEntropyError
          push_cast
          ring
        linarith only [heq, hdiff]
  exact (h.trans hcoefficient).trans (by nlinarith [mul_le_mul_of_nonneg_right herror hnonneg])

theorem eventually_linear_host_forest_error (A : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n m : ℕ) (G : SimpleGraph (Fin n)) (K : SimpleGraph (Fin m)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) → 0 < K.edgeSet.ncard →
      (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard →
      forestCountingError n (Nat.card G.ConnectedComponent) K.edgeSet.ncard (d ^ A) ≤ G.edgeSet.ncard := by
  have he := (polynomialEntropyError_tends_to_zero 0 (A + 4)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp he
  refine ⟨max 1 (max (Nat.ceil M) (Nat.ceil x₀)), ?_⟩
  intro d hd n m G K hn hmin hhost hbudget
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hrest : max (Nat.ceil M) (Nat.ceil x₀) ≤ d := (le_max_right _ _).trans hd
  have hMd : M ≤ (d : ℝ) := (Nat.le_ceil M).trans (by exact_mod_cast (le_max_left _ _).trans hrest)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_right _ _).trans hrest)
  have hdata := hx₀ d hx
  have hmin' : ∀ v, d ≤ G.degree v := by simpa only [G.ncard_neighborSet] using hmin
  have hhost' : 0 < K.edgeFinset.card := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hhost
  have hbudget' : (K.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hbudget
  simpa only [Fintype.card_fin, K.edgeFinset_card, Set.fintypeCard_eq_ncard] using
    linear_host_forest_error G K A d M hd1 hM hMd hmin' hhost' hbudget' hdata.le

end Erdos911
