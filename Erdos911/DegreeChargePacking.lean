import Erdos911.GraphCounting

namespace Erdos911

theorem injective_degree_sum_le {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (f : I → V) (hf : Function.Injective f) :
    (∑ i, K.degree (f i)) ≤ 2 * K.edgeFinset.card := by
  classical
  have heq : (∑ v ∈ (Finset.univ : Finset I).image f, K.degree v) = ∑ i, K.degree (f i) :=
    Finset.sum_image (fun i _ j _ hij => hf hij)
  rw [← heq, ← K.sum_degrees_eq_twice_card_edges]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

/-- Positive retained weight and strict charge on every retained block
give a strict global degree-sum lower bound. -/
theorem retained_degree_charge_bound {I : Type*} [Fintype I]
    (B : Finset I) (w d : I → ℕ) (Γ D : ℕ)
    (hpos : 0 < ∑ i, w i) (hweight : 7 * (∑ i, w i) ≤ 8 * (∑ i ∈ B, w i))
    (hcharge : ∀ i ∈ B, Γ * w i < d i) (hbudget : (∑ i, d i) ≤ D) :
    7 * Γ * (∑ i, w i) < 8 * D := by
  classical
  have hB : B.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hweight
    omega
  obtain ⟨i₀, hi₀⟩ := hB
  have hs : Γ * (∑ i ∈ B, w i) < ∑ i ∈ B, d i := by
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum (fun i hi => (hcharge i hi).le) ⟨i₀, hi₀, hcharge i₀ hi₀⟩
  have hd : (∑ i ∈ B, d i) ≤ D :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (fun _ _ _ => Nat.zero_le _)).trans hbudget
  have hm := Nat.mul_le_mul_left Γ hweight
  nlinarith only [hs, hd, hm]

end Erdos911
