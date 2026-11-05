import Erdos911.HereditaryDensity

namespace Erdos911

noncomputable def hereditaryDegreeCutoff (Λ : ℝ) (Δ : ℕ) : ℕ :=
  Nat.ceil (4096 * Λ * Real.log ((Δ : ℝ) + 1)) + 4

theorem hereditaryDegreeCutoff_bounds (Λ : ℝ) (Δ : ℕ) (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) :
    4 ≤ hereditaryDegreeCutoff Λ Δ ∧
      Λ ≤ denseWitnessMultiplier (hereditaryDegreeCutoff Λ Δ) Δ ∧
      (hereditaryDegreeCutoff Λ Δ : ℝ) ≤ 4096 * Λ * Real.log ((Δ : ℝ) + 1) + 5 := by
  have hlog := log_successor_ge_half Δ hΔ
  have hden : 0 < 4096 * Real.log ((Δ : ℝ) + 1) := by linarith
  have hlower := Nat.le_ceil (4096 * Λ * Real.log ((Δ : ℝ) + 1))
  have hupper := (Nat.ceil_lt_add_one
    (show 0 ≤ 4096 * Λ * Real.log ((Δ : ℝ) + 1) by positivity)).le
  refine ⟨by unfold hereditaryDegreeCutoff; omega, ?_, ?_⟩
  · unfold denseWitnessMultiplier
    apply (le_div_iff₀ hden).mpr
    unfold hereditaryDegreeCutoff
    push_cast
    nlinarith
  · unfold hereditaryDegreeCutoff
    push_cast
    linarith

/-- A target admitting a small size-Ramsey multiplier has bounded density
on all of its subgraphs, independently of their order. -/
theorem global_subgraph_density_bound {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (G : SimpleGraph U) [DecidableRel G.Adj] (hFG : F.IsContained G)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hmax : ∀ v, G.degree v ≤ Δ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ Λ * G.edgeSet.ncard) :
    (F.edgeSet.ncard : ℝ) ≤
      (2048 * Λ * Real.log ((Δ : ℝ) + 1) + 5 / 2) * Fintype.card V := by
  classical
  by_cases hk : 0 < Fintype.card V
  · obtain ⟨hd, hmult, hupper⟩ := hereditaryDegreeCutoff_bounds Λ Δ hΛ hΔ
    have hbound := hereditary_average_degree_bound F G hFG (hereditaryDegreeCutoff Λ Δ) Δ
      hd hk hmax Λ hmult hRamsey
    have hreal : (2 : ℝ) * F.edgeSet.ncard <
        (hereditaryDegreeCutoff Λ Δ : ℝ) * Fintype.card V := by exact_mod_cast hbound
    have hscale := mul_le_mul_of_nonneg_right hupper
      (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
    nlinarith
  · have hzero : Fintype.card V = 0 := Nat.eq_zero_of_not_pos hk
    let : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero
    have hF : F = ⊥ := by ext u; exact isEmptyElim u
    simp [hF]

theorem global_induced_density_bound {U : Type*} [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hmax : ∀ v, G.degree v ≤ Δ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ Λ * G.edgeSet.ncard) (S : Finset U) :
    ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤
      (2048 * Λ * Real.log ((Δ : ℝ) + 1) + 5 / 2) * S.card := by
  classical
  have hcard : Fintype.card (S : Set U) = S.card := by simp
  simpa only [hcard] using global_subgraph_density_bound
    (G.induce (S : Set U)) G ⟨SimpleGraph.Copy.induce G (S : Set U)⟩ Δ hΔ hmax Λ hΛ hRamsey

end Erdos911
