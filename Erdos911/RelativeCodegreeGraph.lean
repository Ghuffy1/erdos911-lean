import Erdos911.IncidenceCodegrees

namespace Erdos911

/-- A relative codegree threshold compares common rows with the larger
weight of the two endpoints. Eligibility is kept explicit. -/
noncomputable def relativeCodegreeGraph {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (A : Finset L) (w : L → ℝ) (C : ℝ) : SimpleGraph L where
  Adj x z := x ≠ z ∧ x ∈ A ∧ z ∈ A ∧ max (w x) (w z) ≤ C * incidenceCodegree N x z
  symm.symm x z h := ⟨h.1.symm, h.2.2.1, h.2.1, by
    simpa only [max_comm, incidenceCodegree_symm N z x] using h.2.2.2⟩
  loopless.irrefl _ h := h.1 rfl

theorem relativeCodegreeGraph_adj {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (A : Finset L) (w : L → ℝ) (C : ℝ) (x z : L) :
    (relativeCodegreeGraph N A w C).Adj x z ↔
      x ≠ z ∧ x ∈ A ∧ z ∈ A ∧ max (w x) (w z) ≤ C * incidenceCodegree N x z := Iff.rfl

/-- The relative threshold cancels the endpoint weight. In particular,
no upper bound on the weights or on the number of rows is required. -/
theorem relativeCodegreeGraph_degree_le {L R : Type*}
    [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (A : Finset L) (w : L → ℝ) (C : ℝ) (D : ℕ)
    (hC : 0 ≤ C) (hrow : ∀ y, (N y).card ≤ D)
    (hcolumn : ∀ x ∈ A, ((incidenceColumn N x).card : ℝ) ≤ w x)
    (hpositive : ∀ x ∈ A, 0 < w x) (x : L) :
    letI : DecidableRel (relativeCodegreeGraph N A w C).Adj := Classical.decRel _
    ((relativeCodegreeGraph N A w C).degree x : ℝ) ≤ C * D := by
  classical
  let Q := relativeCodegreeGraph N A w C
  by_cases hx : x ∈ A
  · have hcharge : w x * Q.degree x ≤ C * (∑ z : L, (incidenceCodegree N x z : ℝ)) := by
      calc
        w x * Q.degree x = ∑ _z ∈ Q.neighborFinset x, w x := by simp [mul_comm]
        _ ≤ ∑ z ∈ Q.neighborFinset x, C * incidenceCodegree N x z := by
          apply Finset.sum_le_sum
          intro z hz
          have hadj := (Q.mem_neighborFinset x z).mp hz
          exact (le_max_left (w x) (w z)).trans hadj.2.2.2
        _ ≤ ∑ z : L, C * incidenceCodegree N x z :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = _ := by rw [Finset.mul_sum]
    have hsum : (∑ z : L, (incidenceCodegree N x z : ℝ)) ≤ (D : ℝ) * (incidenceColumn N x).card := by
      exact_mod_cast incidenceCodegree_sum_le N D hrow x
    have h₁ := mul_le_mul_of_nonneg_left hsum hC
    have h₂ := mul_le_mul_of_nonneg_left (hcolumn x hx) (show 0 ≤ C * (D : ℝ) by positivity)
    have hbound : w x * Q.degree x ≤ w x * (C * D) := by nlinarith only [hcharge, h₁, h₂]
    exact (mul_le_mul_iff_right₀ (hpositive x hx)).mp hbound
  · have hn : Q.neighborFinset x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hx ((Q.mem_neighborFinset x z).mp hz).2.1
    have hz : Q.degree x = 0 := by rw [← Q.card_neighborFinset_eq_degree, hn, Finset.card_empty]
    change (Q.degree x : ℝ) ≤ C * D
    rw [hz, Nat.cast_zero]
    positivity

end Erdos911
