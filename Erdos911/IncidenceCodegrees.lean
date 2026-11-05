import Erdos911.IncidenceGraph
import Erdos911.FiniteDegreeColoring

namespace Erdos911

noncomputable def incidenceColumn {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (x : L) : Finset R := by
  classical
  exact Finset.univ.filter (fun y => x ∈ N y)

noncomputable def incidenceCodegree {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (x z : L) : ℕ := by
  classical
  exact (incidenceColumn N x ∩ incidenceColumn N z).card

theorem incidenceCodegree_symm {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (x z : L) : incidenceCodegree N x z = incidenceCodegree N z x := by
  classical
  simp only [incidenceCodegree, Finset.inter_comm]

theorem incidenceColumn_card {L R : Type*} [DecidableEq L] [Fintype L] [DecidableEq R] [Fintype R]
    (N : R → Finset L) (x : L) : (incidenceColumn N x).card = (incidenceGraph N).degree (Sum.inl x) := by
  rw [incidenceGraph_degree_left]
  rfl

/-- Sum of codegrees at a left vertex equals the sum of row sizes
through that vertex, including the diagonal codegree. -/
theorem incidenceCodegree_sum {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (x : L) :
    (∑ z, incidenceCodegree N x z) = ∑ y ∈ incidenceColumn N x, (N y).card := by
  classical
  have hpair (z : L) : incidenceCodegree N x z = ∑ y : R, if x ∈ N y ∧ z ∈ N y then 1 else 0 := by
    have heq : incidenceColumn N x ∩ incidenceColumn N z =
        Finset.univ.filter (fun y => x ∈ N y ∧ z ∈ N y) := by
      apply Finset.ext
      intro y
      simp only [incidenceColumn, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [incidenceCodegree, heq]
    simp
  simp_rw [hpair]
  rw [Finset.sum_comm]
  unfold incidenceColumn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : x ∈ N y
  · simp [hx]
  · simp [hx]

theorem incidenceCodegree_sum_le {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (d : ℕ) (hrow : ∀ y, (N y).card ≤ d) (x : L) :
    (∑ z, incidenceCodegree N x z) ≤ d * (incidenceColumn N x).card := by
  rw [incidenceCodegree_sum]
  calc
    _ ≤ ∑ _y ∈ incidenceColumn N x, d := Finset.sum_le_sum (fun y _ => hrow y)
    _ = _ := by simp [mul_comm]

theorem incidenceCodegree_off_diagonal {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (d : ℕ) (hd : 1 ≤ d) (hrow : ∀ y, (N y).card = d) (x : L) :
    (∑ z ∈ (Finset.univ : Finset L).erase x, incidenceCodegree N x z) =
      (d - 1) * (incidenceColumn N x).card := by
  classical
  have hsum : (∑ z, incidenceCodegree N x z) = d * (incidenceColumn N x).card := by
    rw [incidenceCodegree_sum]
    simp [hrow, mul_comm]
  have hdiag : incidenceCodegree N x x = (incidenceColumn N x).card := by simp [incidenceCodegree]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset L) (incidenceCodegree N x) (Finset.mem_univ x)
  rw [hdiag, hsum] at hsplit
  have hd1 : d = d - 1 + 1 := by omega
  rw [hd1, add_mul, one_mul] at hsplit
  omega

noncomputable def heavyIncidenceGraph {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) : SimpleGraph L where
  Adj x z := x ≠ z ∧ W ≤ incidenceCodegree N x z
  symm.symm x z h := ⟨h.1.symm, by simpa only [incidenceCodegree_symm N x z] using h.2⟩
  loopless.irrefl x h := h.1 rfl

/-- The total codegree charge bounds the degree of the heavy-pair graph. -/
theorem heavyIncidenceGraph_degree_charge {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (d : ℕ) (hrow : ∀ y, (N y).card ≤ d) (x : L) :
    letI : DecidableRel (heavyIncidenceGraph N W).Adj := Classical.decRel _
    W * (heavyIncidenceGraph N W).degree x ≤ (d : ℝ) * (incidenceColumn N x).card := by
  classical
  let Q := heavyIncidenceGraph N W
  calc
    W * Q.degree x = ∑ _z ∈ Q.neighborFinset x, W := by simp [mul_comm]
    _ ≤ ∑ z ∈ Q.neighborFinset x, (incidenceCodegree N x z : ℝ) := by
      apply Finset.sum_le_sum
      intro z hz
      exact ((Q.mem_neighborFinset x z).mp hz).2
    _ ≤ ∑ z : L, (incidenceCodegree N x z : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun z _ _ => Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast incidenceCodegree_sum_le N d hrow x

end Erdos911
