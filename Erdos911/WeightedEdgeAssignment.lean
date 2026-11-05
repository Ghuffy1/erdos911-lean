import Erdos911.RestrictedStarCounting
import Mathlib.Data.Finset.Max

namespace Erdos911

theorem weighted_incidence_sum {I E : Type*} [Fintype I] [Fintype E]
    [DecidableEq I] [DecidableEq E] (R : I → Finset E) (w : I → ℝ) :
    (∑ i, ((R i).card : ℝ) * w i) = ∑ e, ∑ i, if e ∈ R i then w i else 0 := by
  have hrow (i : I) : ((R i).card : ℝ) * w i = ∑ e, if e ∈ R i then w i else 0 := by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ : Finset E).filter (fun e => e ∈ R i) = R i := by ext e; simp
    rw [hfilter, Finset.sum_const, nsmul_eq_mul]
  simp_rw [hrow]
  exact Finset.sum_comm

/-- Assign each claimed edge to a claimant of maximum weight. If an edge
has at most `r` claimants, the weighted assigned mass keeps at least a
`1/r` fraction of the weighted claimed mass, expressed without division. -/
theorem exists_weighted_disjoint_assignment {I E : Type*}
    [Fintype I] [Nonempty I] [Fintype E] [DecidableEq I] [DecidableEq E]
    (R : I → Finset E) (w : I → ℝ) (r : ℕ) (hw : ∀ i, 0 ≤ w i)
    (hoverlap : ∀ e, ((Finset.univ : Finset I).filter (fun i => e ∈ R i)).card ≤ r) :
    ∃ D : I → Finset E, (∀ i, D i ⊆ R i) ∧
      ((Finset.univ : Finset I) : Set I).PairwiseDisjoint D ∧
      Finset.univ.biUnion D = Finset.univ.biUnion R ∧
      (∑ i, ((R i).card : ℝ) * w i) ≤ r * ∑ i, ((D i).card : ℝ) * w i := by
  classical
  let S := Finset.univ.biUnion R
  have hex : ∀ e : E, ∃ i : I, (∃ j, e ∈ R j) →
      e ∈ R i ∧ ∀ j, e ∈ R j → w j ≤ w i := by
    intro e
    by_cases hclaim : ∃ j, e ∈ R j
    · let claimants := (Finset.univ : Finset I).filter (fun i => e ∈ R i)
      have hnonempty : claimants.Nonempty := by
        obtain ⟨i, hi⟩ := hclaim
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image claimants w hnonempty
      refine ⟨i, fun _ => ⟨(Finset.mem_filter.mp hi).2, ?_⟩⟩
      intro j hj
      exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
    · exact ⟨Classical.choice ‹Nonempty I›, fun h => (hclaim h).elim⟩
  choose owner howner using hex
  let D := fun i => S.filter (fun e => owner e = i)
  have hclaim_of_mem {e : E} (he : e ∈ S) : ∃ i, e ∈ R i := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact ⟨i, hi⟩
  have hsubset : ∀ i, D i ⊆ R i := by
    intro i e he
    obtain ⟨heS, hi⟩ := Finset.mem_filter.mp he
    have h := (howner e (hclaim_of_mem heS)).1
    simpa only [hi] using h
  have hdisjoint : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint D := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact hij ((Finset.mem_filter.mp hei).2.symm.trans (Finset.mem_filter.mp hej).2)
  have hcover : Finset.univ.biUnion D = S := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp hi).1
    · intro e he
      exact Finset.mem_biUnion.mpr ⟨owner e, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  refine ⟨D, hsubset, hdisjoint, hcover, ?_⟩
  rw [weighted_incidence_sum R w, weighted_incidence_sum D w, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hassigned : (∑ i, if e ∈ D i then w i else 0) =
      if e ∈ S then w (owner e) else 0 := by
    simp only [D, Finset.mem_filter]
    by_cases he : e ∈ S
    · simp only [he, true_and]
      simp
    · simp only [he, false_and, ite_false, Finset.sum_const_zero]
  rw [hassigned]
  by_cases he : e ∈ S
  · rw [ite_eq_left he, ← Finset.sum_filter]
    have hmax := (howner e (hclaim_of_mem he)).2
    calc
      (∑ i ∈ (Finset.univ : Finset I).filter (fun i => e ∈ R i), w i) ≤
          ∑ _i ∈ (Finset.univ : Finset I).filter (fun i => e ∈ R i), w (owner e) :=
        Finset.sum_le_sum (fun i hi => hmax i (Finset.mem_filter.mp hi).2)
      _ = (((Finset.univ : Finset I).filter (fun i => e ∈ R i)).card : ℝ) * w (owner e) := by simp
      _ ≤ r * w (owner e) := mul_le_mul_of_nonneg_right (by exact_mod_cast hoverlap e) (hw _)
  · have hnone : ∀ i, e ∉ R i := by
      intro i hi
      exact he (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)
    simp only [hnone, he, ite_false, Finset.sum_const_zero, mul_zero, le_refl]

theorem disjoint_assignment_reconstruction {I E : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq E]
    (F : Finset E) (A D : I → Finset E)
    (hsubset : ∀ i, D i ⊆ F) (hallowed : ∀ i, D i ⊆ A i)
    (hdisjoint : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint D) :
    F ∈ restrictedStarSubsets F A (F.card - ∑ i, (D i).card) (fun i => (D i).card) ∧
      F.card = (F.card - ∑ i, (D i).card) + ∑ i, (D i).card := by
  classical
  let U := Finset.univ.biUnion D
  have hU : U ⊆ F := by
    intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact hsubset i hi
  have hcard : U.card = ∑ i, (D i).card := Finset.card_biUnion hdisjoint
  have hle : (∑ i, (D i).card) ≤ F.card := hcard ▸ Finset.card_le_card hU
  refine ⟨?_, (Nat.sub_add_cancel hle).symm⟩
  apply (mem_restrictedStarSubsets F A _ _ F).mpr
  refine ⟨F \ U, D, Finset.sdiff_subset, ?_, fun i => ⟨hallowed i, rfl⟩, ?_⟩
  · rw [Finset.card_sdiff_of_subset hU, hcard]
  · exact (Finset.sdiff_union_of_subset hU).symm

end Erdos911
