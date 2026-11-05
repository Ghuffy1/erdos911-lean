import Erdos911.IncidenceTypeGaps
import Erdos911.IncidenceJointPruning
import Erdos911.NearRegularJointPruning

namespace Erdos911

/-- The three incidence tests can be removed together at a cost of at
most one sixteenth of the target's edge budget. -/
theorem incidence_joint_pruning (A : ℕ) (M τ : ℝ) (hM : 1 ≤ M) (hτ : 0 < τ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V W : Type*)
    [Fintype V] [Fintype W] [DecidableEq W], ∀ k a e D P : ℕ,
      d ≤ k → 0 < a → a ≤ k → 0 < e → 0 < D → D ≤ d ^ A →
      (d : ℝ) * k ≤ 2 * e → (e : ℝ) ≤ (d : ℝ) * k →
      32 * M * (d : ℝ) ^ 2 ≤ (P : ℝ) → (P : ℝ) ≤ 64 * M * (d : ℝ) ^ 2 →
      τ * Real.log (Real.log d) ≤ Real.log ((k : ℝ) / a) →
      ∀ (G : SimpleGraph V) (H J K : SimpleGraph W)
      [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj], H ≤ K →
      ∀ (blocks : Finset (RectangleBlock W)) (E : ℝ),
      BoundedEdgeBlocks blocks (nearRegularBlockSize d * nearRegularBlockSize d) →
      (∀ w, H.degree w ≤ D) →
      (∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k) →
      0 ≤ E → (H.edgeFinset.card : ℝ) ≤ (M * d) * E →
      Real.exp ((e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
        ((componentClass G k e).card : ℝ) →
      ∃ t ∈ componentClass G k e,
        ((incidenceJointBadSupport G H J K blocks (nearRegularRepeatThreshold d e)
          (tolerantTupleOrder d) D P a e ((e : ℝ) / 128)
          ((e : ℝ) / 128 * Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) t).card : ℝ) ≤
            (1 / 16 : ℝ) * E ∧
        ∀ f : (componentModel G t).Copy
          (H.deleteEdges (incidenceJointBadSupport G H J K blocks (nearRegularRepeatThreshold d e)
            (tolerantTupleOrder d) D P a e ((e : ℝ) / 128)
            ((e : ℝ) / 128 * Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) t : Set (Sym2 W))),
          let fH := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
          (copyRawEdges fH ∉ orientationPatterns H K P (copyVertices fH) a e ((e : ℝ) / 128)) ∧
            (¬3 * nearRegularRepeatThreshold d e ≤ repeatedEdgeVolume blocks (copyRawEdges fH)) ∧
            copyRawEdges fH ∉ starImagePatterns H J (copyVertices fH) (tolerantTupleOrder d) e D P
              ((e : ℝ) / 128 * Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) := by
  obtain ⟨dG, hdG⟩ := incidence_type_gaps A M τ hM hτ
  obtain ⟨dP, hdP⟩ := near_regular_pruning_parameters_uniform
  obtain ⟨dR, hdR⟩ := near_regular_bad_support_rate_uniform (3 * M / 2)
  refine ⟨max 2 (max dG (max dP dR)), ?_⟩
  intro d hd V W _ _ _ k a e D P hk ha hak he hD hDpow haverage hupper hlower hPlarge horient
    G H J K _ _ _ hHK blocks E hblocks hmax hlocal hE hbudget hclass
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  obtain ⟨_, _, _, hja, hj, _⟩ := hdP d (by omega) k e hk haverage
  obtain ⟨ho, hs, hr⟩ := hdG d (by omega) k a e D P (nearRegularRepeatThreshold d e)
    hk ha he hD hDpow haverage hupper hlower hPlarge horient hj
  have hPpos : 0 < P := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h : (0 : ℝ) < P := (show 0 < 32 * M * (d : ℝ) ^ 2 by positivity).trans_le hlower
    exact_mod_cast h
  have hkpos : 0 < k := by omega
  have hqpos : 0 < nearRegularBlockSize d := by
    have h := (nearRegularBlockSize_bounds d (by omega)).1
    omega
  let T := (e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)
  let ℓ := (e : ℝ) / 128 * Real.log ((P : ℝ) / incidenceCommonCutoff A P d)
  have htwo := joint_type_count_log_gap (tolerantTupleOrder d) k e (nearRegularRepeatThreshold d e)
    D P (nearRegularBlockSize d * nearRegularBlockSize d) ℓ T e hkpos hD hPpos
    (Nat.mul_pos hqpos hqpos) hja hr hs
  have hone : orientationBadTypeBound P k a e D ((e : ℝ) / 128) ≤ Real.exp T * Real.exp (-(e : ℝ)) := by
    rw [orientationBadTypeBound_eq_exp P k a e D _ hD]
    simpa only [T, sub_eq_add_neg, Real.exp_add] using Real.exp_le_exp.mpr ho
  have hcounts :
      (orientationBadTypeBound P k a e D ((e : ℝ) / 128) +
        repeatedTypeCountBoundForEdges k e (nearRegularRepeatThreshold d e) D (P * k)
          (nearRegularBlockSize d * nearRegularBlockSize d)) +
        starBadTypeBound (tolerantTupleOrder d) k e D P ℓ ≤
          3 * Real.exp T * Real.exp (-(e : ℝ)) := by
    nlinarith only [htwo, hone]
  have heLarge : (d : ℝ) ≤ e := by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
    have h := mul_le_mul_of_nonneg_left hk2 (Nat.cast_nonneg (α := ℝ) d)
    nlinarith only [h, haverage]
  have hdecay : Real.exp (-(e : ℝ)) ≤ Real.exp (-(d : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have hrate : 3 * (M * d) * Real.exp (-(e : ℝ)) ≤ (1 / 16 : ℝ) := by
    have h := (mul_le_mul_of_nonneg_left hdecay (show 0 ≤ 3 * M * (d : ℝ) by positivity)).trans
      (by simpa only [show 2 * (3 * M / 2) * (d : ℝ) = 3 * M * d by ring] using hdR d (by omega))
    simpa only [mul_assoc] using h
  have hclasspos : (componentClass G k e).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.exp_pos T).trans_le hclass
  have hcost : (H.edgeFinset.card : ℝ) *
      ((orientationBadTypeBound P k a e D ((e : ℝ) / 128) +
        repeatedTypeCountBoundForEdges k e (nearRegularRepeatThreshold d e) D (P * k)
          (nearRegularBlockSize d * nearRegularBlockSize d)) +
        starBadTypeBound (tolerantTupleOrder d) k e D P ℓ) ≤
      (1 / 16 : ℝ) * E * (componentClass G k e).card := by
    calc
      _ ≤ ((M * d) * E) * (3 * Real.exp T * Real.exp (-(e : ℝ))) :=
        mul_le_mul hbudget hcounts (by
          unfold orientationBadTypeBound repeatedTypeCountBoundForEdges starBadTypeBound
          positivity) (by positivity)
      _ = (E * Real.exp T) * (3 * (M * d) * Real.exp (-(e : ℝ))) := by ring
      _ ≤ (E * Real.exp T) * (1 / 16) := mul_le_mul_of_nonneg_left hrate (by positivity)
      _ = (1 / 16 : ℝ) * E * Real.exp T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hclass (by positivity)
  obtain ⟨t, ht, hsmall, hgood⟩ := exists_incidence_joint_pruned_type G H J K hHK blocks
    (nearRegularBlockSize d * nearRegularBlockSize d) hblocks (nearRegularRepeatThreshold d e)
    (tolerantTupleOrder d) k a e D P ((e : ℝ) / 128) ℓ (1 / 16) E ha he hPpos hak
    hmax hlocal hclasspos hcost
  have hte : componentSize G t = e := ((Finset.mem_filter.mp ht).2).2
  refine ⟨t, ht, hsmall, ?_⟩
  intro f
  simpa only [hte] using hgood f

end Erdos911
