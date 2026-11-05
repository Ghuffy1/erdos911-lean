import Erdos911.IncidenceCodegrees

namespace Erdos911

def orderedRowPairCount {L R : Type*} [DecidableEq L] [Fintype L]
    (N : R → Finset L) (Q : SimpleGraph L) [DecidableRel Q.Adj] (y : R) : ℕ :=
  ∑ x ∈ N y, ((N y).filter (fun z => Q.Adj x z)).card

noncomputable def orderedCodegreeWeight {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (Q : SimpleGraph L) [DecidableRel Q.Adj] : ℕ :=
  ∑ x : L, ∑ z : L, if Q.Adj x z then incidenceCodegree N x z else 0

theorem incidenceCodegree_as_sum {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (x z : L) :
    incidenceCodegree N x z = ∑ y : R, if x ∈ N y ∧ z ∈ N y then 1 else 0 := by
  classical
  have heq : incidenceColumn N x ∩ incidenceColumn N z =
      Finset.univ.filter (fun y => x ∈ N y ∧ z ∈ N y) := by
    apply Finset.ext
    intro y
    simp only [incidenceColumn, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [incidenceCodegree, heq]
  simp

theorem orderedRowPairCount_as_sum {L R : Type*} [DecidableEq L] [Fintype L]
    (N : R → Finset L) (Q : SimpleGraph L) [DecidableRel Q.Adj] (y : R) :
    orderedRowPairCount N Q y =
      ∑ x : L, ∑ z : L, if Q.Adj x z ∧ x ∈ N y ∧ z ∈ N y then 1 else 0 := by
  classical
  have hinner (x : L) : ((N y).filter (fun z => Q.Adj x z)).card =
      ∑ z : L, if z ∈ N y ∧ Q.Adj x z then 1 else 0 := by
    have heq : (N y).filter (fun z => Q.Adj x z) =
        Finset.univ.filter (fun z => z ∈ N y ∧ Q.Adj x z) := by
      apply Finset.ext
      intro z
      simp
    rw [heq]
    simp
  unfold orderedRowPairCount
  simp_rw [hinner]
  have hfilter : (Finset.univ : Finset L).filter (fun x => x ∈ N y) = N y := by ext x; simp
  have houter : (∑ x ∈ N y, ∑ z : L, if z ∈ N y ∧ Q.Adj x z then 1 else 0) =
      ∑ x : L, if x ∈ N y then (∑ z : L, if z ∈ N y ∧ Q.Adj x z then 1 else 0) else 0 := by
    symm
    rw [← Finset.sum_filter, hfilter]
  rw [houter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ N y
  · simp only [hx, ite_true, true_and]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ N y <;> by_cases ha : Q.Adj x z <;> simp [hz, ha]
  · simp [hx]

/-- Double counting the pair-row incidences converts weighted codegrees
into the number of ordered graph edges inside the rows. -/
theorem orderedCodegreeWeight_eq_sum_rows {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) (Q : SimpleGraph L) [DecidableRel Q.Adj] :
    orderedCodegreeWeight N Q = ∑ y, orderedRowPairCount N Q y := by
  classical
  have hterm (x z : L) : (if Q.Adj x z then incidenceCodegree N x z else 0) =
      ∑ y : R, if Q.Adj x z ∧ x ∈ N y ∧ z ∈ N y then 1 else 0 := by
    rw [incidenceCodegree_as_sum]
    by_cases h : Q.Adj x z <;> simp [h]
  unfold orderedCodegreeWeight
  simp_rw [hterm]
  calc
    _ = ∑ x : L, ∑ y : R, ∑ z : L,
        if Q.Adj x z ∧ x ∈ N y ∧ z ∈ N y then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ y : R, ∑ x : L, ∑ z : L,
        if Q.Adj x z ∧ x ∈ N y ∧ z ∈ N y then 1 else 0 := Finset.sum_comm
    _ = _ := by simp_rw [orderedRowPairCount_as_sum]

theorem sum_incidenceColumn_card {L R : Type*} [DecidableEq L] [Fintype L] [Fintype R]
    (N : R → Finset L) : (∑ x : L, (incidenceColumn N x).card) = ∑ y : R, (N y).card := by
  classical
  have hcol (x : L) : (incidenceColumn N x).card = ∑ y : R, if x ∈ N y then 1 else 0 := by
    simp [incidenceColumn]
  simp_rw [hcol]
  rw [Finset.sum_comm]
  simp

end Erdos911
