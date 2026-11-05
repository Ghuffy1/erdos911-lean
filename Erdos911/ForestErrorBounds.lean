import Erdos911.LowEntropyColoring

namespace Erdos911

theorem log_counting_term_bound (x M B N : ℝ)
    (hx : 0 ≤ x) (hxN : x ≤ N) (hM : 0 < M) (hMB : M ≤ B)
    (hN : 0 < N) (hNB : N ≤ B) :
    x * Real.log (M / x) + x ≤ N * (Real.log (B / N) + 1) := by
  have hB : 0 < B := hN.trans_le hNB
  have hlog : 0 ≤ Real.log (B / N) :=
    Real.log_nonneg ((le_div_iff₀ hN).mpr (by simpa using hNB))
  by_cases hxzero : x = 0
  · simp only [hxzero, div_zero, Real.log_zero, zero_mul, zero_add]
    positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hcompare : Real.log (M / x) ≤ Real.log (B / x) :=
    Real.log_le_log (div_pos hM hxpos) (div_le_div_of_nonneg_right hMB hx)
  have hsplit : Real.log (B / x) = Real.log (B / N) + Real.log (N / x) := by
    rw [Real.log_div hB.ne' hxpos.ne', Real.log_div hB.ne' hN.ne',
      Real.log_div hN.ne' hxpos.ne']
    ring
  have hratio := Real.log_le_sub_one_of_pos (div_pos hN hxpos)
  have hmulratio := mul_le_mul_of_nonneg_left hratio hx
  have hcancel : x * (N / x) = N := by field_simp
  have hmulcompare := mul_le_mul_of_nonneg_left hcompare hx
  have hmulmax := mul_le_mul_of_nonneg_right hxN hlog
  rw [hsplit] at hmulcompare
  nlinarith

/-- A uniform bound for the forest correction when the host has at most
`Λ` times the target edge count and the target order is at most `2e/d`. -/
theorem forestCountingError_bound (n r m Δ : ℕ) (e Λ d : ℝ)
    (hr : r ≤ n) (hm : 0 < m) (hΔ : 1 ≤ Δ)
    (he : 0 < e) (hΛ : 1 ≤ Λ) (hd : 1 ≤ d)
    (hn : (n : ℝ) ≤ 2 * e / d) (hbudget : (m : ℝ) ≤ Λ * e) :
    forestCountingError n r m Δ ≤
      (2 * e / d) * (2 * (Real.log (Λ * d) + 1) + Real.log Δ) := by
  let N := 2 * e / d
  let B := 2 * Λ * e
  have hdpos : 0 < d := by linarith
  have hN : 0 < N := by dsimp [N]; positivity
  have hNB : N ≤ B := by
    have hΛd : 1 ≤ Λ * d := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hΛ) (sub_nonneg.mpr hd)]
    dsimp only [N, B]
    apply (div_le_iff₀ hdpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hΛd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he.le)]
  have hM : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hMB : (2 * m : ℝ) ≤ B := by dsimp only [B]; linarith
  have hrN : (r : ℝ) ≤ N := (by exact_mod_cast hr : (r : ℝ) ≤ n).trans hn
  have hsN : ((n - r : ℕ) : ℝ) ≤ N :=
    (by exact_mod_cast Nat.sub_le n r : ((n - r : ℕ) : ℝ) ≤ n).trans hn
  have hroot := log_counting_term_bound r (2 * m) B N
    (Nat.cast_nonneg r) hrN hM hMB hN hNB
  have hnonroot := log_counting_term_bound ((n - r : ℕ) : ℝ) (2 * m) B N
    (Nat.cast_nonneg _) hsN hM hMB hN hNB
  have hlogΔ : 0 ≤ Real.log Δ := Real.log_nonneg (by exact_mod_cast hΔ)
  have hdegree := mul_le_mul_of_nonneg_right hsN hlogΔ
  have hratio : B / N = Λ * d := by
    dsimp only [B, N]
    field_simp
  calc
    forestCountingError n r m Δ ≤ 2 * N * (Real.log (B / N) + 1) + N * Real.log Δ := by
      unfold forestCountingError
      nlinarith [Nat.cast_nonneg (α := ℝ) (n - r)]
    _ = (2 * e / d) * (2 * (Real.log (Λ * d) + 1) + Real.log Δ) := by
      rw [hratio]
      dsimp only [N]
      ring

theorem graph_forest_error_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (d Δ : ℕ) (hd : 1 ≤ d) (hΔ : 1 ≤ Δ)
    (hmin : ∀ v, d ≤ G.degree v) (hhost : 0 < H.edgeFinset.card)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hbudget : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard) :
    forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent)
      H.edgeFinset.card Δ ≤
      (2 * G.edgeSet.ncard / d) * (2 * (Real.log (Λ * d) + 1) + Real.log Δ) := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hv : 0 < G.degree v := lt_of_lt_of_le (by omega) (hmin v)
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hv
  have hedge : ∃ u w, G.Adj u w := ⟨v, w, hw⟩
  have he : (0 : ℝ) < G.edgeSet.ncard := by
    exact_mod_cast (Set.ncard_pos (s := G.edgeSet)).mpr ⟨s(v, w), hw⟩
  have hn : (Fintype.card V : ℝ) ≤ 2 * G.edgeSet.ncard / d := by
    apply (le_div_iff₀ (by exact_mod_cast (show 0 < d by omega) : (0 : ℝ) < d)).mpr
    have hsum : d * Fintype.card V ≤ 2 * G.edgeFinset.card := by
      calc
        d * Fintype.card V = ∑ _ : V, d := by simp [mul_comm]
        _ ≤ ∑ u, G.degree u := Finset.sum_le_sum (fun u _ => hmin u)
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
    exact_mod_cast (by simpa [mul_comm] using hsum)
  exact forestCountingError_bound (Fintype.card V) (Nat.card G.ConnectedComponent)
    H.edgeFinset.card Δ G.edgeSet.ncard Λ d (components_lt_vertices_of_adj G hedge).le
    hhost hΔ he hΛ (by exact_mod_cast hd) hn hbudget

end Erdos911
