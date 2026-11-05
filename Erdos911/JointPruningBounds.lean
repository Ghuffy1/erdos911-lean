import Erdos911.JointTypePruning
import Erdos911.StarPruningBounds
import Erdos911.RepeatedTypeBounds

namespace Erdos911

/-- A common logarithmic gap controls the sum of the two bad-type counts. -/
theorem joint_type_count_log_gap (s k a j D P R : ℕ) (L T gap : ℝ)
    (hk : 0 < k) (hD : 0 < D) (hP : 0 < P) (hR : 0 < R) (hja : 2 * j ≤ a)
    (hrepeat : repeatedTypeExponent k a j D (P * k) R ≤ T - gap)
    (hstar : starBadTypeLogBound s k a D P L ≤ T - gap) :
    repeatedTypeCountBoundForEdges k a j D (P * k) R + starBadTypeBound s k a D P L ≤
      2 * Real.exp T * Real.exp (-gap) := by
  have hcount : repeatedTypeCountBoundForEdges k a j D (P * k) R ≤
      Real.exp (T - gap) := by
    apply le_trans ?_ (Real.exp_le_exp.mpr hrepeat)
    simpa only [repeatedTypeCountBoundForEdges, Nat.cast_mul, Nat.cast_pow] using
      repeatedTypeCount_le_exp k a j D (P * k) R hD (Nat.mul_pos hP hk) hR hja
  have hstarCount : starBadTypeBound s k a D P L ≤ Real.exp (T - gap) := by
    rw [starBadTypeBound_eq_exp s k a D P L hD]
    exact Real.exp_le_exp.mpr hstar
  calc
    _ ≤ 2 * Real.exp (T - gap) := by linarith only [hcount, hstarCount]
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

theorem exists_joint_pruned_type_of_log_gap {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (blocks : Finset (RectangleBlock W)) (R : ℕ) (hblocks : BoundedEdgeBlocks blocks R)
    (j s k a D P : ℕ) (L T gap Λ E η : ℝ)
    (hk : 0 < k) (ha : 0 < a) (hDpos : 0 < D) (hP : 0 < P) (hR : 0 < R)
    (hja : 2 * j ≤ a) (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : Real.exp T ≤ ((componentClass G k a).card : ℝ))
    (hrepeat : repeatedTypeExponent k a j D (P * k) R ≤ T - gap)
    (hstar : starBadTypeLogBound s k a D P L ≤ T - gap)
    (hΛ : 0 ≤ Λ) (hE : 0 ≤ E) (hη : 0 ≤ η)
    (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * E)
    (hrate : 2 * Λ * Real.exp (-gap) ≤ η) :
    ∃ t ∈ componentClass G k a, ((jointBadSupport G H J blocks j s P L t).card : ℝ) ≤ η * E ∧
      ∀ f : (componentModel G t).Copy
          (H.deleteEdges (jointBadSupport G H J blocks j s P L t : Set (Sym2 W))),
        (¬3 * j ≤ repeatedEdgeVolume blocks (copyRawEdges
          ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))) ∧
        ¬IsStarDeficitImage H J
          (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
          (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) s P L := by
  have hbad := joint_type_count_log_gap s k a j D P R L T gap hk hDpos hP hR hja hrepeat hstar
  have hclasspos : (componentClass G k a).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.exp_pos T).trans_le hclass
  have hbudget : (H.edgeFinset.card : ℝ) *
      (repeatedTypeCountBoundForEdges k a j D (P * k) R + starBadTypeBound s k a D P L) ≤
        η * E * (componentClass G k a).card := by
    calc
      _ ≤ (Λ * E) * (2 * Real.exp T * Real.exp (-gap)) :=
        mul_le_mul hhost hbad (by unfold repeatedTypeCountBoundForEdges starBadTypeBound; positivity)
          (mul_nonneg hΛ hE)
      _ = (E * Real.exp T) * (2 * Λ * Real.exp (-gap)) := by ring
      _ ≤ (E * Real.exp T) * η :=
        mul_le_mul_of_nonneg_left hrate (mul_nonneg hE (Real.exp_pos T).le)
      _ = η * E * Real.exp T := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hclass (mul_nonneg hη hE)
  exact exists_joint_pruned_type_of_bounded G H J blocks R hblocks j s k a D P L η E
    ha hP hD hlocal hclasspos hbudget

end Erdos911
