import Erdos911.GraphCounting

namespace Erdos911

/-- The degree-sum bound also applies to weighted, injectively mapped
roles. The weights need only have a common upper bound. -/
theorem high_image_weight_sum_le {I W : Type*}
    [DecidableEq I] [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (f : I → W)
    (hf : Function.Injective f) (S : Finset I) (w : I → ℝ)
    (D : ℕ) (Δ Λ e : ℝ) (hD : 0 < D) (hΔ : 0 ≤ Δ) (he : 0 ≤ e)
    (hweight : ∀ i ∈ S, w i ≤ Δ)
    (himages : ∀ i ∈ S, D ≤ K.degree (f i))
    (hbudget : (K.edgeSet.ncard : ℝ) ≤ Λ * e)
    (hcutoff : 16 * Λ * Δ ≤ (D : ℝ)) :
    (∑ i ∈ S, w i) ≤ e / 8 := by
  classical
  let H := (Finset.univ : Finset W).filter (fun v => D ≤ K.degree v)
  have hS : S.card ≤ H.card := by
    calc
      S.card = (S.image f).card := (Finset.card_image_of_injective S hf).symm
      _ ≤ H.card := Finset.card_le_card (by
        intro v hv
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, himages i hi⟩)
  have hmass := (Nat.mul_le_mul_left D hS).trans (high_degree_card_bound K D)
  rw [K.edgeFinset_card, Set.fintypeCard_eq_ncard] at hmass
  have hmassR : (D : ℝ) * S.card ≤ 2 * K.edgeSet.ncard := by exact_mod_cast hmass
  have hsum : (∑ i ∈ S, w i) ≤ Δ * S.card := by
    simpa [mul_comm] using Finset.sum_le_sum hweight
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have h₁ := mul_le_mul_of_nonneg_left hsum hDp.le
  have h₂ := mul_le_mul_of_nonneg_left hmassR hΔ
  have h₃ := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 2 * Δ by positivity)
  have h₄ := mul_le_mul_of_nonneg_right hcutoff (show 0 ≤ e / 8 by positivity)
  have hfinal : (D : ℝ) * (∑ i ∈ S, w i) ≤ (D : ℝ) * (e / 8) := by
    nlinarith only [h₁, h₂, h₃, h₄]
  nlinarith only [hfinal, hDp]

/-- A set of target roles mapped to high-degree host vertices has small
total target degree. Real degree bounds avoid a rounding loss. -/
theorem high_image_degree_mass_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph W) [DecidableRel K.Adj]
    (f : G.Copy K) (S : Finset V) (D : ℕ) (Δ Λ : ℝ)
    (hD : 0 < D) (hΔ : 0 ≤ Δ)
    (hdegree : ∀ v ∈ S, (G.degree v : ℝ) ≤ Δ)
    (himages : ∀ v ∈ S, D ≤ K.degree (f v))
    (hbudget : (K.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hcutoff : 16 * Λ * Δ ≤ (D : ℝ)) :
    (∑ v ∈ S, (G.degree v : ℝ)) ≤ (G.edgeSet.ncard : ℝ) / 8 := by
  classical
  let H := (Finset.univ : Finset W).filter (fun w => D ≤ K.degree w)
  have hS : S.card ≤ H.card := by
    calc
      S.card = (S.image f).card := (Finset.card_image_of_injective S f.injective).symm
      _ ≤ H.card := Finset.card_le_card (by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, himages v hv⟩)
  have hmass := (Nat.mul_le_mul_left D hS).trans (high_degree_card_bound K D)
  rw [K.edgeFinset_card, Set.fintypeCard_eq_ncard] at hmass
  have hmassR : (D : ℝ) * S.card ≤ 2 * K.edgeSet.ncard := by exact_mod_cast hmass
  have hsum : (∑ v ∈ S, (G.degree v : ℝ)) ≤ Δ * S.card := by
    have hs := Finset.sum_le_sum hdegree
    simpa [mul_comm] using hs
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have h₁ := mul_le_mul_of_nonneg_left hsum hDp.le
  have h₂ := mul_le_mul_of_nonneg_left hmassR hΔ
  have h₃ := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 2 * Δ by positivity)
  have h₄ := mul_le_mul_of_nonneg_right hcutoff (show 0 ≤ (G.edgeSet.ncard : ℝ) / 8 by positivity)
  have hfinal : (D : ℝ) * (∑ v ∈ S, (G.degree v : ℝ)) ≤ (D : ℝ) * ((G.edgeSet.ncard : ℝ) / 8) := by
    nlinarith only [h₁, h₂, h₃, h₄]
  nlinarith only [hfinal, hDp]

end Erdos911
