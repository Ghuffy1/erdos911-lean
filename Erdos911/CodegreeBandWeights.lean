import Erdos911.ReverseCodegreeBands

namespace Erdos911

theorem adjacency_indicator_sum {L : Type*} [Fintype L] [DecidableEq L]
    (Q : SimpleGraph L) [DecidableRel Q.Adj] (x : L) :
    (∑ z : L, if Q.Adj x z then (1 : ℕ) else 0) = Q.degree x := by
  classical
  have hset : (Finset.univ : Finset L).filter (Q.Adj x) = Q.neighborFinset x := by
    apply Finset.ext
    intro z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
  rw [← Finset.sum_filter, hset]
  simp

theorem orderedCodegreeWeight_le_edge_bound {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (Q : SimpleGraph L) [DecidableRel Q.Adj] (t : ℝ)
    (hbound : ∀ x z, Q.Adj x z → (incidenceCodegree N x z : ℝ) ≤ t) :
    (orderedCodegreeWeight N Q : ℝ) ≤ 2 * t * Q.edgeSet.ncard := by
  classical
  have hcount : (∑ x : L, ∑ z : L, if Q.Adj x z then (1 : ℕ) else 0) = 2 * Q.edgeSet.ncard := by
    simp_rw [adjacency_indicator_sum]
    rw [Q.sum_degrees_eq_twice_card_edges, Q.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have hreal : (∑ x : L, ∑ z : L, if Q.Adj x z then (1 : ℝ) else 0) = 2 * Q.edgeSet.ncard := by
    exact_mod_cast hcount
  calc
    (orderedCodegreeWeight N Q : ℝ) =
        ∑ x : L, ∑ z : L, if Q.Adj x z then (incidenceCodegree N x z : ℝ) else 0 := by
      unfold orderedCodegreeWeight
      push_cast
      rfl
    _ ≤ ∑ x : L, ∑ z : L, if Q.Adj x z then t else 0 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro z _
      by_cases h : Q.Adj x z <;> simp only [h, ite_true, ite_false, le_refl]
      exact hbound x z h
    _ = t * (∑ x : L, ∑ z : L, if Q.Adj x z then (1 : ℝ) else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
    _ = _ := by rw [hreal]; ring

theorem positiveCodegreeGraph_weight_eq {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (Q : SimpleGraph L) [DecidableRel Q.Adj] :
    letI : DecidableRel (positiveCodegreeGraph N Q).Adj := Classical.decRel _
    orderedCodegreeWeight N (positiveCodegreeGraph N Q) = orderedCodegreeWeight N Q := by
  classical
  unfold orderedCodegreeWeight
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  simp only [positiveCodegreeGraph_adj]
  by_cases h : Q.Adj x z
  · by_cases hp : 0 < incidenceCodegree N x z
    · simp only [h, hp, and_self, ite_true]
    · have hz : incidenceCodegree N x z = 0 := by omega
      simp [h, hz]
  · simp only [h, false_and, ite_false]

/-- Weighted, rather than merely unweighted, edge mass is preserved by
an arbitrary finite edge partition. -/
theorem orderedCodegreeWeight_partition {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (Q : SimpleGraph L) [DecidableRel Q.Adj]
    (index : Sym2 L → ℕ) (n : ℕ) (hindex : ∀ x z, Q.Adj x z → index s(x, z) < n) :
    orderedCodegreeWeight N Q = ∑ j : Fin n, orderedCodegreeWeight N (indexedEdgeGraph Q index j.val) := by
  classical
  have hpoint (x z : L) : (if Q.Adj x z then incidenceCodegree N x z else 0) =
      ∑ j : Fin n, if (indexedEdgeGraph Q index j.val).Adj x z then incidenceCodegree N x z else 0 := by
    by_cases h : Q.Adj x z
    · have hi := hindex x z h
      have heq (j : Fin n) : index s(x, z) = j.val ↔ j = ⟨index s(x, z), hi⟩ := by
        constructor
        · intro h
          exact Fin.ext h.symm
        · rintro rfl
          rfl
      simp only [indexedEdgeGraph_adj, h, true_and, ite_true, heq]
      simp
    · simp only [indexedEdgeGraph_adj, h, false_and, ite_false, Finset.sum_const_zero]
  unfold orderedCodegreeWeight
  conv_lhs => simp only [hpoint]
  calc
    _ = ∑ x : L, ∑ j : Fin n, ∑ z : L,
        if (indexedEdgeGraph Q index j.val).Adj x z then incidenceCodegree N x z else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- Positive light-pair mass splits exactly across the reverse dyadic
bands. Zero-codegree pairs contribute zero before and after the split. -/
theorem reverseCodegreeBand_weight_partition {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (n : ℕ) (hW : W ≤ (2 : ℝ) ^ n) :
    letI : DecidableRel (lightIncidenceGraph N W).Adj := Classical.decRel _
    letI : ∀ j : Fin n, DecidableRel (reverseCodegreeBand N W n j.val).Adj := fun _ => Classical.decRel _
    orderedCodegreeWeight N (lightIncidenceGraph N W) =
      ∑ j : Fin n, orderedCodegreeWeight N (reverseCodegreeBand N W n j.val) := by
  classical
  have hidx (x z : L) (h : (positiveCodegreeGraph N (lightIncidenceGraph N W)).Adj x z) :
      n - 1 - Nat.log 2 (incidencePairCodegree N s(x, z)) < n := by
    have hpos : 0 < incidenceCodegree N x z := h.2
    have hupper : (incidenceCodegree N x z : ℝ) < W := h.1.2
    have hlt : incidenceCodegree N x z < 2 ^ n := by exact_mod_cast hupper.trans_le hW
    have hlog := Nat.log_lt_of_lt_pow hpos.ne' hlt
    rw [incidencePairCodegree_mk]
    omega
  have h := orderedCodegreeWeight_partition N (positiveCodegreeGraph N (lightIncidenceGraph N W))
    (fun e => n - 1 - Nat.log 2 (incidencePairCodegree N e)) n hidx
  have heq := positiveCodegreeGraph_weight_eq N (lightIncidenceGraph N W)
  convert heq.symm.trans h using 1
  apply Finset.sum_congr rfl
  intro j _
  unfold orderedCodegreeWeight reverseCodegreeBand
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

end Erdos911
