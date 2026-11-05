import Erdos911.ForestErrorBounds

namespace Erdos911

noncomputable def biasedEntropyThreshold (d Δ : ℕ) (Λ p η : ℝ) : ℝ :=
  (1 - η) * (-Real.log p - 2 * (1 / (d : ℝ))) -
    (2 / (d : ℝ)) * (2 * (Real.log (Λ * d) + 1) + Real.log Δ)

/-- A necessary entropy bound with no dependence on the order or component
orders beyond their contribution to the target's edge count. -/
theorem ramsey_uniform_component_entropy_lower_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (d Δ D : ℕ) (hd : 4 ≤ d) (hD : 2 ≤ D) (hΔ : 1 ≤ Δ)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (hhost : 0 < H.edgeFinset.card) (hRamsey : RamseyFor G G H)
    (Λ p η : ℝ) (hΛ : 1 ≤ Λ) (hp₀ : 0 < p) (hp : p ≤ 1 / 2)
    (hscale : 16 * Real.log D ≤ p * d)
    (hbudget : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hprune : (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) ≤
      η * G.edgeSet.ncard) :
    (G.edgeSet.ncard : ℝ) * biasedEntropyThreshold d Δ Λ p η ≤ componentEntropyMass G := by
  have hbase := ramsey_component_entropy_lower_bound G H d Δ D hd hD hmin hmax
    hhost hRamsey p η hp₀ hp hscale hprune
  have herror := graph_forest_error_bound G H d Δ (by omega) hΔ hmin hhost Λ hΛ hbudget
  unfold biasedEntropyThreshold
  simp only [div_eq_mul_inv] at hbase herror ⊢
  nlinarith

theorem uniform_low_entropy_coloring {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (d Δ D : ℕ) (hd : 4 ≤ d) (hD : 2 ≤ D) (hΔ : 1 ≤ Δ)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (hhost : 0 < H.edgeFinset.card)
    (Λ p η : ℝ) (hΛ : 1 ≤ Λ) (hp₀ : 0 < p) (hp : p ≤ 1 / 2)
    (hscale : 16 * Real.log D ≤ p * d)
    (hbudget : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hprune : (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) ≤
      η * G.edgeSet.ncard)
    (hentropy : componentEntropyMass G <
      (G.edgeSet.ncard : ℝ) * biasedEntropyThreshold d Δ Λ p η) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  have herror := graph_forest_error_bound G H d Δ (by omega) hΔ hmin hhost Λ hΛ hbudget
  have hlogbudget : componentEntropyMass G +
      forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent)
        H.edgeFinset.card Δ +
      ((1 - η) * G.edgeSet.ncard) * (Real.log p + 2 * (1 / (d : ℝ))) < 0 := by
    unfold biasedEntropyThreshold at hentropy
    simp only [div_eq_mul_inv] at herror hentropy ⊢
    nlinarith
  exact minimum_degree_entropy_coloring G H d Δ D hd hD hmin hmax hhost p η
    hp₀ hp hscale hprune hlogbudget

end Erdos911
