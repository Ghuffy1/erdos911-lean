import Erdos911.ConditionalSeedAvoidance
import Erdos911.EligibleBlueImages
import Erdos911.BiasedForestColoring

open MeasureTheory

namespace Erdos911

/-- The conditional seed test controls full blue copies even when the
red graph also contains edges outside the residual variable graph. -/
theorem conditional_seed_avoiding_coloring {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph U) [DecidableRel F.Adj]
    (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hHK : H ≤ K) (hJH : J ≤ H) (hFG : F.IsContained G) (hF : F.Connected)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s q b : ℕ) (τ p : ℝ)
    (hτ : 0 < τ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * seedAssignmentCountBound (Fintype.card U) Δ D s q / p) ≤ p * b / 2)
    (hcoverage : ∀ f : F.Copy H, ∃ a : SeedAssignment F H J s τ q,
      PartialAssignmentAgrees a.2.val f ∧ b ≤ (partialAssignmentEdges F J a.2.val).card)
    (L : ℝ)
    (hdeleted : ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ L)
    (hbase : p * Real.exp (p / 4) ≤ 1)
    (hbudget : (K.copyCount G : ℝ) * (p * Real.exp (p / 4)) ^
      Nat.ceil ((G.edgeSet.ncard : ℝ) - L) < 1) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  let μ := bitProductMeasure J.edgeSet p hp₀.le hp₁
  let Good := seedAssignmentGood F H J s τ q b
  let images := eligibleCopyImages G K H J
  let t := Nat.ceil ((G.edgeSet.ncard : ℝ) - L)
  let B (E : images) := fixedBits (retainedEdges J E.val) true
  obtain ⟨hpositive, hconditional⟩ := seed_assignment_conditional_avoidance F H J hJH hF
    Δ D hΔ hD hΔpos hDpos s q b τ p hτ hp₀ hp₁ hlog
  have hbase₀ : 0 ≤ p * Real.exp (p / 4) := (mul_pos hp₀ (Real.exp_pos _)).le
  have hB : ∀ E : images, μ.real (B E ∩ Good) / μ.real Good ≤ (p * Real.exp (p / 4)) ^ t := by
    intro E
    have hsize : t ≤ (retainedEdges J E.val).card :=
      Nat.ceil_le.mpr (eligible_image_residual_card G K H J L hdeleted E.val E.property)
    exact (hconditional (retainedEdges J E.val)).trans
      (pow_le_pow_of_le_one hbase₀ hbase hsize)
  have hcount : (Fintype.card images : ℝ) ≤ K.copyCount G := by
    rw [Fintype.card_coe]
    exact_mod_cast eligibleCopyImages_card_le G K H J
  have hbudget' : (Fintype.card images : ℝ) * (p * Real.exp (p / 4)) ^ t < 1 :=
    (mul_le_mul_of_nonneg_right hcount (pow_nonneg hbase₀ t)).trans_lt hbudget
  obtain ⟨ω, hω, hnotblue⟩ := exists_avoiding_inside_event μ Good hpositive B
    ((p * Real.exp (p / 4)) ^ t) hB hbudget'
  let R := H \ edgeColorClass J ω true
  refine ⟨R, sdiff_le.trans hHK, ?_, ?_⟩
  · intro hG
    exact seedAssignmentGood_no_copy F H J s τ q b hcoverage ω hω (hFG.trans hG)
  · rintro ⟨f⟩
    let fK : G.Copy K := (SimpleGraph.Copy.ofLE _ K sdiff_le).comp f
    have hE : copyRawEdges fK ∈ images := blue_copy_eligible G K H J ω f
    exact hnotblue ⟨copyRawEdges fK, hE⟩ (blue_copy_residual_bits G K H J hJH ω f)

/-- The full-target spanning-forest count closes the blue union bound
after conditioning on the residual seed events. -/
theorem conditional_seed_entropy_coloring {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph U) [DecidableRel F.Adj]
    (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hHK : H ≤ K) (hJH : J ≤ H) (hFG : F.IsContained G) (hF : F.Connected)
    (ΔG Δ D : ℕ) (hΔG : ∀ v, G.degree v ≤ ΔG)
    (hhost : 0 < K.edgeFinset.card) (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v)
    (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s q b : ℕ) (τ p : ℝ)
    (hτ : 0 < τ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * seedAssignmentCountBound (Fintype.card U) Δ D s q / p) ≤ p * b / 2)
    (hcoverage : ∀ f : F.Copy H, ∃ a : SeedAssignment F H J s τ q,
      PartialAssignmentAgrees a.2.val f ∧ b ≤ (partialAssignmentEdges F J a.2.val).card)
    (L : ℝ)
    (hdeleted : ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ L)
    (hbase : p * Real.exp (p / 4) ≤ 1)
    (hbudget : componentEntropyMass G + forestCountingError (Fintype.card V)
      (Nat.card G.ConnectedComponent) K.edgeFinset.card ΔG +
      ((G.edgeSet.ncard : ℝ) - L) * (Real.log p + p / 4) < 0) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  have hlogbase : Real.log (p * Real.exp (p / 4)) = Real.log p + p / 4 := by
    rw [Real.log_mul hp₀.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hcount := copyCount_le_forest_entropy G K ΔG hΔG hhost hneighbors hedge
  have hpower := power_budget_of_log_budget (K.copyCount G)
    (componentEntropyMass G + forestCountingError (Fintype.card V)
      (Nat.card G.ConnectedComponent) K.edgeFinset.card ΔG)
    (p * Real.exp (p / 4)) ((G.edgeSet.ncard : ℝ) - L)
    (Nat.ceil ((G.edgeSet.ncard : ℝ) - L)) hcount (mul_pos hp₀ (Real.exp_pos _))
    hbase (Nat.le_ceil _) (by simpa only [hlogbase] using hbudget)
  exact conditional_seed_avoiding_coloring G F K H J hHK hJH hFG hF Δ D hΔ hD hΔpos hDpos
    s q b τ p hτ hp₀ hp₁ hlog hcoverage L hdeleted hbase hpower

end Erdos911
