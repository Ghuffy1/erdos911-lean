import Erdos911.StarTypePruning

namespace Erdos911

noncomputable def starBadTypeLogBound (s k a D P : ℕ) (L : ℝ) : ℝ :=
  ((2 * (k - 1) : ℕ) : ℝ) * Real.log D +
    ((s * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ) +
    (k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ) +
    (a : ℝ) * Real.log ((P * k : ℝ) / a) - L + 2 * a

theorem starBadTypeBound_eq_exp (s k a D P : ℕ) (L : ℝ) (hD : 0 < D) :
    starBadTypeBound s k a D P L = Real.exp (starBadTypeLogBound s k a D P L) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hfirst : (D : ℝ) ^ (2 * (k - 1)) =
      Real.exp (((2 * (k - 1) : ℕ) : ℝ) * Real.log D) := by
    rw [Real.exp_nat_mul, Real.exp_log hDreal]
  have hsecond : (((D ^ 2 + 1) ^ (s * k) : ℕ) : ℝ) =
      Real.exp (((s * k : ℕ) : ℝ) * Real.log ((D ^ 2 + 1 : ℕ) : ℝ)) := by
    rw [Nat.cast_pow, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hthird : ((D + 1 : ℕ) : ℝ) ^ k =
      Real.exp ((k : ℝ) * Real.log ((D + 1 : ℕ) : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  unfold starBadTypeBound starBadTypeLogBound
  rw [hfirst, hsecond, hthird, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- A class exponent exceeding the bad-type exponent by `gap` pays for
the deleted support whenever the host multiplier times `exp(-gap)` does. -/
theorem exists_star_pruned_type_of_log_gap {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s k a D P : ℕ) (L T gap Λ E η : ℝ) (ha : 0 < a) (hP : 0 < P) (hDpos : 0 < D)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : Real.exp T ≤ ((componentClass G k a).card : ℝ))
    (hgap : starBadTypeLogBound s k a D P L ≤ T - gap)
    (hΛ : 0 ≤ Λ) (hE : 0 ≤ E) (hη : 0 ≤ η)
    (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * E) (hrate : Λ * Real.exp (-gap) ≤ η) :
    ∃ t ∈ componentClass G k a, ((starBadSupport G H J s P L t).card : ℝ) ≤ η * E ∧
      ∀ f : (componentModel G t).Copy
          (H.deleteEdges (starBadSupport G H J s P L t : Set (Sym2 W))),
        ¬IsStarDeficitImage H J
          (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
          (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) s P L := by
  have hbad : starBadTypeBound s k a D P L ≤ Real.exp T * Real.exp (-gap) := by
    rw [starBadTypeBound_eq_exp s k a D P L hDpos]
    simpa only [sub_eq_add_neg, Real.exp_add] using Real.exp_le_exp.mpr hgap
  have hclasspos : (componentClass G k a).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.exp_pos T).trans_le hclass
  have hbudget : (H.edgeFinset.card : ℝ) * starBadTypeBound s k a D P L ≤
      η * E * (componentClass G k a).card := by
    calc
      (H.edgeFinset.card : ℝ) * starBadTypeBound s k a D P L ≤
          (Λ * E) * (Real.exp T * Real.exp (-gap)) :=
        mul_le_mul hhost hbad (by unfold starBadTypeBound; positivity) (mul_nonneg hΛ hE)
      _ = (E * Real.exp T) * (Λ * Real.exp (-gap)) := by ring
      _ ≤ (E * Real.exp T) * η := mul_le_mul_of_nonneg_left hrate (mul_nonneg hE (Real.exp_pos T).le)
      _ = η * E * Real.exp T := by ring
      _ ≤ η * E * (componentClass G k a).card := mul_le_mul_of_nonneg_left hclass (mul_nonneg hη hE)
  exact exists_star_pruned_type G H J s k a D P L η E ha hP hD hlocal hclasspos hbudget

end Erdos911
