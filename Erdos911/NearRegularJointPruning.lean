import Erdos911.NearRegularTypeGaps
import Erdos911.NearRegularPruningParameters
import Erdos911.JointPruningBounds
import Erdos911.LowEndpointDensity

open Filter

namespace Erdos911

theorem near_regular_bad_support_rate_uniform (M : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 2 * M * d * Real.exp (-(d : ℝ)) ≤ (1 / 16 : ℝ) := by
  have hbase : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (nhds 0) := by
    simpa only [Real.rpow_one, neg_one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)
  have hlimit : Tendsto (fun x : ℝ => 2 * M * x * Real.exp (-x)) atTop (nhds 0) := by
    convert hbase.const_mul (2 * M) using 1
    · funext x
      ring
    · simp only [mul_zero]
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (hlimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num)))
  refine ⟨Nat.ceil x₀, ?_⟩
  intro d hd
  exact (hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast hd))).le

/-- The near-regular numerical choices select one component type for
both bad-copy tests, at a total support cost of at most one sixteenth of
the target edge budget. The original host and residual graph are retained
in the star-deficit predicate. -/
theorem near_regular_joint_pruning (A M : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V W : Type*)
    [Fintype V] [Fintype W] [DecidableEq W], ∀ k a D Δ : ℕ,
      d ≤ k → 0 < a → 0 < D → D ≤ d ^ 3 →
      (d : ℝ) * k ≤ 2 * a → 2 * (a : ℝ) ≤ (Δ : ℝ) * k →
      (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
      16 * M * d * Δ ≤ (D : ℝ) → (D : ℝ) ≤ 32 * M * d * Δ →
      ∀ (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
        (blocks : Finset (RectangleBlock W)) (E : ℝ),
      BoundedEdgeBlocks blocks (nearRegularBlockSize d * nearRegularBlockSize d) →
      (∀ w, H.degree w ≤ D) → 0 ≤ E → (H.edgeFinset.card : ℝ) ≤ (M * d) * E →
      Real.exp ((a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
        ((componentClass G k a).card : ℝ) →
      ∃ t ∈ componentClass G k a,
        ((jointBadSupport G H J blocks (nearRegularRepeatThreshold d a) (tolerantTupleOrder d) D
          ((a : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d)) t).card : ℝ) ≤
            (1 / 16 : ℝ) * E ∧
        ∀ f : (componentModel G t).Copy
            (H.deleteEdges (jointBadSupport G H J blocks (nearRegularRepeatThreshold d a)
              (tolerantTupleOrder d) D
              ((a : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d)) t : Set (Sym2 W))),
          (¬3 * nearRegularRepeatThreshold d a ≤ repeatedEdgeVolume blocks (copyRawEdges
            ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))) ∧
          ¬IsStarDeficitImage H J
            (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
            (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
            (tolerantTupleOrder d) D
            ((a : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d)) := by
  obtain ⟨dG, hdG⟩ := near_regular_type_gaps A M hA hM
  obtain ⟨dP, hdP⟩ := near_regular_pruning_parameters_uniform
  obtain ⟨dR, hdR⟩ := near_regular_bad_support_rate_uniform M
  refine ⟨max 2 (max dG (max dP dR)), ?_⟩
  intro d hd V W _ _ _ k a D Δ hk ha hD hDpow haverage hupper hdegree hlower hhost
    G H J _ _ blocks E hblocks hmax hE hbudget hclass
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  have hdG' : dG ≤ d := by omega
  have hdP' : dP ≤ d := by omega
  have hdR' : dR ≤ d := by omega
  obtain ⟨_, _, _, hja, hj, _⟩ := hdP d hdP' k a hk haverage
  obtain ⟨hstar, hrepeat⟩ := hdG d hdG' k a D Δ (nearRegularRepeatThreshold d a)
    hk ha hD hDpow haverage hupper hdegree hlower hhost hj
  have haLarge : (d : ℝ) ≤ a := by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have h := mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg (α := ℝ) d)
    nlinarith only [h, haverage]
  have hdecay : Real.exp (-(a : ℝ)) ≤ Real.exp (-(d : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hMnonneg : 0 ≤ M := by linarith
  have hmult : 0 ≤ 2 * M * (d : ℝ) := by positivity
  have hrate : 2 * (M * d) * Real.exp (-(a : ℝ)) ≤ (1 / 16 : ℝ) := by
    have h := (mul_le_mul_of_nonneg_left hdecay hmult).trans (hdR d hdR')
    simpa only [mul_assoc] using h
  have hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ D * k := by
    intro U hU
    rw [inducedHostEdges_card, ← hU]
    exact induced_edges_le_low_endpoint_degree H D (fun u _ _ => Or.inl (hmax u)) U
  have hqpos : 0 < nearRegularBlockSize d := by
    have h := (nearRegularBlockSize_bounds d (by omega)).1
    omega
  exact exists_joint_pruned_type_of_log_gap G H J blocks
    (nearRegularBlockSize d * nearRegularBlockSize d) hblocks
    (nearRegularRepeatThreshold d a) (tolerantTupleOrder d) k a D D
    ((a : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d))
    ((a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) a (M * d) E (1 / 16)
    (by omega) ha hD hD (Nat.mul_pos hqpos hqpos) hja hmax hlocal hclass hrepeat hstar
    (mul_nonneg hMnonneg (Nat.cast_nonneg _)) hE (by norm_num) hbudget hrate

end Erdos911
