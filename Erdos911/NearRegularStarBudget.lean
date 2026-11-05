import Erdos911.NearRegularTupleProbability
import Erdos911.NeighborhoodSeedMarking

namespace Erdos911

theorem degree_threshold_vertex_budget {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X : Finset W) (T : ℝ)
    (hX : ∀ x ∈ X, T ≤ H.degree x) :
    (X.card : ℝ) * T ≤ 2 * H.edgeSet.ncard := by
  classical
  calc
    _ = ∑ _x ∈ X, T := by simp [mul_comm]
    _ ≤ ∑ x ∈ X, (H.degree x : ℝ) := Finset.sum_le_sum hX
    _ ≤ ∑ x : W, (H.degree x : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = 2 * H.edgeSet.ncard := by
      have h := H.sum_degrees_eq_twice_card_edges
      rw [H.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
      exact_mod_cast h

/-- The concrete mark probability leaves a small fraction of the target
edge budget after the conditional factor of two. -/
theorem near_regular_tuple_capacity_budget (d D Λ Δ X m e : ℝ)
    (hlog : 0 < Real.log d) (hD : 0 < D) (hΛ : 0 < Λ) (hX : 0 ≤ X)
    (hvertices : X * nearRegularCommonCutoff D d ≤ 2 * m)
    (hhost : m ≤ Λ * e) (hcutoff : 16 * Λ * Δ ≤ D) :
    (2 * nearRegularTupleMarkRate D d) * 32 * X * D ^ 128 * Δ ≤ e / 128 := by
  have hz : 0 < (Real.log d) ^ nearRegularLossPower := Real.rpow_pos_of_pos hlog _
  have hnormalized : (2 * nearRegularTupleMarkRate D d) * 32 * X * D ^ 128 * Δ =
      X * Δ / (16 * (Real.log d) ^ nearRegularLossPower) := by
    unfold nearRegularTupleMarkRate tupleMarkRate
    field_simp
    ring
  have hvertices' : X * D ≤ 2 * m * (Real.log d) ^ nearRegularLossPower := by
    apply (div_le_iff₀ hz).mp
    simpa only [nearRegularCommonCutoff, mul_div_assoc] using hvertices
  have hhost' := mul_le_mul_of_nonneg_right hhost (show 0 ≤ 2 * (Real.log d) ^ nearRegularLossPower by positivity)
  have hcutoff' := mul_le_mul_of_nonneg_right hcutoff hX
  have hcharged : 8 * X * Δ ≤ e * (Real.log d) ^ nearRegularLossPower := by
    apply (mul_le_mul_iff_of_pos_left hΛ).mp
    nlinarith only [hvertices', hhost', hcutoff']
  rw [hnormalized]
  apply (div_le_div_iff₀ (show 0 < 16 * (Real.log d) ^ nearRegularLossPower by positivity)
    (show (0 : ℝ) < 128 by norm_num)).mpr
  nlinarith only [hcharged]

end Erdos911
