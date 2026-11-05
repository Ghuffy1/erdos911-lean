import Erdos911.DenseWitnessColoring

namespace Erdos911

theorem palette_initial_pruning_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph W) [DecidableRel K.Adj]
    (Δ D : ℕ) (Λ : ℝ) (hmax : ∀ v, G.degree v ≤ Δ)
    (hbudget : (K.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hcut : 128 * Λ * Δ ≤ (D : ℝ)) (f : G.Copy K) :
    ((copyRawEdges f ∩ (K \ degreePrunedGraph K D).edgeFinset).card : ℝ) ≤
      (G.edgeSet.ncard : ℝ) / 64 := by
  apply (degreePruned_copy_deleted_capacity G K f Δ D hmax).trans
  apply (div_le_iff₀ (show (0 : ℝ) < (D + 1 : ℕ) by positivity)).mpr
  have h₁ := mul_le_mul_of_nonneg_right hbudget (show 0 ≤ 2 * (Δ : ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard)
  rw [K.edgeFinset_card, Set.fintypeCard_eq_ncard]
  push_cast
  nlinarith only [h₁, h₂, Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard]

theorem palette_total_cost_budget (D : ℕ) (Λ e m : ℝ) (hD : 1000 ≤ D)
    (he : 0 ≤ e) (hm : m ≤ Λ * e) (hΛ : Λ ≤ D) :
    64 * (1 / (D : ℝ) ^ 2) * m + (4 / 1000 : ℝ) * e ≤ e := by
  have hDR : (1000 : ℝ) ≤ D := by exact_mod_cast hD
  have hDP : (0 : ℝ) < D := by linarith
  have hratio : Λ / (D : ℝ) ^ 2 ≤ 1 / 1000 := by
    apply (div_le_iff₀ (pow_pos hDP _)).mpr
    nlinarith only [hΛ, hDR]
  have h₁ := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 64 * (1 / (D : ℝ) ^ 2) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hratio he
  have hid : 64 * (1 / (D : ℝ) ^ 2) * (Λ * e) = 64 * (Λ / (D : ℝ) ^ 2 * e) := by ring
  rw [hid] at h₁
  nlinarith only [h₁, h₂, he]

end Erdos911
