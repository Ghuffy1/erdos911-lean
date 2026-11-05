import Erdos911.GraphCounting
import Erdos911.IncidenceGraph

namespace Erdos911

/-- A cheap image has bounded individual degrees and few right images
above eight times its degree-charge scale. -/
theorem cheap_image_degree_bounds {A R V : Type*} [Fintype A] [Fintype R]
    [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : A ⊕ R → V) (Γ : ℕ) (hΓ : 0 < Γ)
    (hcheap : (∑ v : A ⊕ R, K.degree (g v)) ≤ Γ * Fintype.card R) :
    (∀ v, K.degree (g v) ≤ Γ * Fintype.card R) ∧
      8 * ((Finset.univ : Finset R).filter (fun y => 8 * Γ < K.degree (g (Sum.inr y)))).card ≤ Fintype.card R := by
  classical
  have hpoint (v : A ⊕ R) : K.degree (g v) ≤ Γ * Fintype.card R :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans hcheap
  refine ⟨hpoint, ?_⟩
  let H := (Finset.univ : Finset R).filter (fun y => 8 * Γ < K.degree (g (Sum.inr y)))
  have hsumR : (∑ y : R, K.degree (g (Sum.inr y))) ≤ Γ * Fintype.card R := by
    rw [Fintype.sum_sum_type] at hcheap
    omega
  have hmass : 8 * Γ * H.card ≤ Γ * Fintype.card R := by
    calc
      8 * Γ * H.card = ∑ _y ∈ H, 8 * Γ := by simp [mul_comm]
      _ ≤ ∑ y ∈ H, K.degree (g (Sum.inr y)) :=
        Finset.sum_le_sum (fun y hy => (Finset.mem_filter.mp hy).2.le)
      _ ≤ ∑ y : R, K.degree (g (Sum.inr y)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun _ _ _ => Nat.zero_le _)
      _ ≤ _ := hsumR
  have hmul : Γ * (8 * H.card) ≤ Γ * Fintype.card R := by nlinarith only [hmass]
  exact Nat.le_of_mul_le_mul_left hmul hΓ

end Erdos911
