import Erdos911.LightIncidenceMass

namespace Erdos911

theorem heavyIncidenceBall_eq_closedNeighborFinset {L R : Type*}
    [DecidableEq L] [Fintype L] [Fintype R]
    (S : R → Finset L) (W : ℝ) (x : L) :
    letI : DecidableRel (heavyIncidenceGraph S W).Adj := Classical.decRel _
    heavyIncidenceBall S W x = closedNeighborFinset (heavyIncidenceGraph S W) x := by
  classical
  ext z
  simp only [mem_heavyIncidenceBall, closedNeighborFinset, Finset.mem_insert]
  rw [(heavyIncidenceGraph S W).mem_neighborFinset]
  rfl

/-- A single square-color class of witnessing centers captures many
concentrated rows, with disjoint left balls and exactly q retained edges
in each selected row. -/
theorem exists_heavy_row_packing {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] [Nonempty L]
    (S : R → Finset L) (W : ℝ) (q D : ℕ)
    (hdegree : letI : DecidableRel (heavyIncidenceGraph S W).Adj := Classical.decRel _
      ∀ x, (heavyIncidenceGraph S W).degree x ≤ D) :
    ∃ (U : Finset R) (f : R → L) (N : R → Finset L),
      (heavyConcentratedRows S W q).card ≤ (D * (D + 1) + 1) * U.card ∧
      (∀ y, N y ⊆ S y) ∧
      (∀ y ∈ U, (N y).card = q ∧ N y ⊆ heavyIncidenceBall S W (f y)) ∧
      (∀ y ∉ U, N y = ∅) ∧
      (∀ y ∈ U, ∀ z ∈ U, f y ≠ f z →
        Disjoint (heavyIncidenceBall S W (f y)) (heavyIncidenceBall S W (f z))) ∧
      (∀ x, (heavyIncidenceBall S W x).card ≤ D + 1) := by
  classical
  let C := heavyConcentratedRows S W q
  let x₀ : L := Classical.choice inferInstance
  have hex (y : R) (hy : y ∈ C) : ∃ x : L, q ≤ (S y ∩ heavyIncidenceBall S W x).card :=
    (Finset.mem_filter.mp hy).2
  let f : R → L := fun y => if hy : y ∈ C then Classical.choose (hex y hy) else x₀
  have hf (y : R) (hy : y ∈ C) : q ≤ (S y ∩ heavyIncidenceBall S W (f y)).card := by
    simpa only [f, hy, dite_true] using Classical.choose_spec (hex y hy)
  obtain ⟨c, hc⟩ := exists_disjoint_closed_neighborhood_coloring (heavyIncidenceGraph S W) D hdegree
  obtain ⟨a, ha⟩ := exists_large_assignment_fiber C (fun y => c (f y))
  let U := C.filter (fun y => c (f y) = a)
  have hU (y : R) (hy : y ∈ U) : y ∈ C := (Finset.mem_filter.mp hy).1
  have hsubset (y : R) (hy : y ∈ U) :
      ∃ T ⊆ S y ∩ heavyIncidenceBall S W (f y), T.card = q :=
    Finset.exists_subset_card_eq (hf y (hU y hy))
  let N : R → Finset L := fun y => if hy : y ∈ U then Classical.choose (hsubset y hy) else ∅
  have hN (y : R) (hy : y ∈ U) :
      N y ⊆ S y ∩ heavyIncidenceBall S W (f y) ∧ (N y).card = q := by
    simpa only [N, hy, dite_true] using Classical.choose_spec (hsubset y hy)
  refine ⟨U, f, N, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using ha
  · intro y
    by_cases hy : y ∈ U
    · exact (hN y hy).1.trans Finset.inter_subset_left
    · simp only [N, hy, dite_false, Finset.empty_subset]
  · intro y hy
    exact ⟨(hN y hy).2, (hN y hy).1.trans Finset.inter_subset_right⟩
  · intro y hy
    simp only [N, hy, dite_false]
  · intro y hy z hz hne
    have heq : c (f y) = c (f z) := (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hz).2.symm
    simpa only [heavyIncidenceBall_eq_closedNeighborFinset] using hc (f y) (f z) hne heq
  · intro x
    rw [heavyIncidenceBall_eq_closedNeighborFinset, closedNeighborFinset_card]
    exact Nat.add_le_add_right (hdegree x) 1

end Erdos911
