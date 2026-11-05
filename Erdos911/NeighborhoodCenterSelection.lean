import Erdos911.NeighborhoodTupleSupply

namespace Erdos911

/-- Common-neighborhood moments select a candidate with many adjacent
centers, each of which sees nearly the whole current candidate list. -/
theorem select_candidate_centers {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (Y : Finset W) (s : ℕ) (D T : ℝ)
    (hs : 2 ≤ s) (hY : Y.Nonempty) (hDpos : 0 < D) (hTpos : 0 < T)
    (hD : ∀ x ∈ Y, ((commonCenters H.Adj {x}).card : ℝ) ≤ D)
    (hcommon : ∀ Z ⊆ Y, Z.card ≤ s → T ≤ ((commonCenters H.Adj Z).card : ℝ))
    (hθ : Real.log (2 * D / T) / ((s - 1 : ℕ) : ℝ) ≤ 1 / 2) :
    ∃ x ∈ Y, ∃ U : Finset W, T / 4 ≤ (U.card : ℝ) ∧
      (∀ u ∈ U, H.Adj x u) ∧
      ∀ u ∈ U,
        (1 - Real.log (2 * D / T) / ((s - 1 : ℕ) : ℝ)) * Y.card ≤
          ((Y.filter (fun y => H.Adj y u)).card : ℝ) := by
  classical
  let θ := Real.log (2 * D / T) / ((s - 1 : ℕ) : ℝ)
  let C := Finset.univ.filter (fun u : W =>
    1 - θ ≤ ((candidatesAt H.Adj Y u).card : ℝ) / Y.card)
  have hC : T / 2 ≤ (C.card : ℝ) :=
    candidate_list_centers H.Adj Y s D T hs hY hDpos hTpos hD hcommon (by linarith)
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hrow : ∀ u ∈ C, (1 - θ) * Y.card ≤ ((Y.filter (fun y => H.Adj y u)).card : ℝ) := by
    intro u hu
    have h := (le_div_iff₀ hYpos).mp (Finset.mem_filter.mp hu).2
    have heq : candidatesAt H.Adj Y u = Y.filter (fun y => H.Adj y u) := by
      ext y
      simp only [candidatesAt, Finset.mem_filter]
    simpa only [heq] using h
  have hsum : (1 - θ) * Y.card * C.card ≤
      ∑ y ∈ Y, ((C.filter (H.Adj y)).card : ℝ) := by
    calc
      _ = ∑ _u ∈ C, (1 - θ) * Y.card := by simp; ring
      _ ≤ ∑ u ∈ C, ((Y.filter (fun y => H.Adj y u)).card : ℝ) := Finset.sum_le_sum hrow
      _ = ∑ y ∈ Y, ((C.filter (H.Adj y)).card : ℝ) := by
        exact_mod_cast (incidence_card_sum_comm Y C H.Adj).symm
  have hex : ∃ x ∈ Y, (1 - θ) * C.card ≤ ((C.filter (H.Adj x)).card : ℝ) := by
    by_contra hn
    push Not at hn
    have hstrict := Finset.sum_lt_sum_of_nonempty hY hn
    simp only [Finset.sum_const, nsmul_eq_mul] at hstrict
    nlinarith only [hsum, hstrict]
  obtain ⟨x, hx, hmass⟩ := hex
  refine ⟨x, hx, C.filter (H.Adj x), ?_, ?_, ?_⟩
  · have hhalf : (1 / 2 : ℝ) * C.card ≤ (1 - θ) * C.card :=
      mul_le_mul_of_nonneg_right (by dsimp only [θ]; linarith) (Nat.cast_nonneg _)
    linarith
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u hu
    exact hrow u (Finset.mem_filter.mp hu).1

end Erdos911
