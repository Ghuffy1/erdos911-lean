import Erdos911.TupleNeighborCoverage

namespace Erdos911

theorem tupleWitnessCapacity_pos {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : V → W) (v : V)
    {s : ℕ} (q : Fin s → Option W) (P : ℕ) (hP : 0 < P) (hdegree : 0 < G.degree v)
    (hhalf : (G.degree v : ℝ) ≤ 2 * (tupleGoodNeighbors G J f v q).card) :
    0 < starWitnessCapacity J P q := by
  classical
  unfold starWitnessCapacity
  split_ifs
  · exact hP
  · have hdegreeR : (0 : ℝ) < G.degree v := by exact_mod_cast hdegree
    have hgood : (tupleGoodNeighbors G J f v q).Nonempty := by
      apply Finset.card_pos.mp
      have hpos : (0 : ℝ) < (tupleGoodNeighbors G J f v q).card := by linarith
      exact_mod_cast hpos
    obtain ⟨u, hu⟩ := hgood
    exact Finset.card_pos.mpr ⟨f u, tupleGoodNeighbors_common_mem G J f v u q hu⟩

theorem starWitnessTuples_of_dense_slots {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (f : G.Copy H) (v : V) {s : ℕ} (q : Fin s → Option W)
    (ε : ℝ) (hε : ε < 1) (hdegree : 0 < G.degree v)
    (hlarge : ∀ i, (1 - ε) * G.degree v ≤ (slotGoodNeighbors G J f v (q i)).card) :
    q ∈ starWitnessTuples H (f v) s := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  cases hqi : q i with
  | none =>
    rw [optionalTwoStepNeighbors]
    exact Finset.mem_insert_self _ _
  | some x =>
    have hpositive : (0 : ℝ) < (1 - ε) * G.degree v :=
      mul_pos (by linarith) (by exact_mod_cast hdegree)
    have hnonempty : (slotGoodNeighbors G J f v (q i)).Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast hpositive.trans_le (hlarge i)
    obtain ⟨u, hu⟩ := hnonempty
    obtain ⟨huv, hx⟩ := (mem_slotGoodNeighbors G J f v u (q i)).mp hu
    have hnear : x ∈ twoStepNeighbors H (f v) := by
      apply (mem_twoStepNeighbors H (f v) x).mpr
      exact ⟨f u, map_rel f.toHom huv, (hJ (hx x hqi)).symm⟩
    rw [optionalTwoStepNeighbors]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hnear, rfl⟩)

/-- Dense candidate tuples give the image-level bad-copy condition used
by the verified star-support pruning theorem. -/
theorem copy_star_deficit_of_dense_tuples {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (f : G.Copy H) (s P : ℕ) (L ε : ℝ) (q : V → Fin s → Option W)
    (hP : 0 < P) (hε : ε < 1) (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hdegree : ∀ v, 0 < G.degree v)
    (hlarge : ∀ v i, (1 - ε) * G.degree v ≤ (slotGoodNeighbors G J f v (q v i)).card)
    (hupper : ∀ v, ¬inactiveStarTuple (q v) → (tupleCommonNeighbors J (q v)).card ≤ P)
    (hdeficit : 4 * L ≤ ∑ v, (G.degree v : ℝ) *
      Real.log ((P : ℝ) / starWitnessCapacity J P (q v))) :
    IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P L := by
  classical
  have hhalf (v : V) : (G.degree v : ℝ) ≤ 2 * (tupleGoodNeighbors G J f v (q v)).card :=
    tupleGoodNeighbors_half_card G J f v (q v) ε hbudget (hlarge v)
  have hcapacity (v : V) : 0 < starWitnessCapacity J P (q v) ∧ starWitnessCapacity J P (q v) ≤ P := by
    refine ⟨tupleWitnessCapacity_pos G J f v (q v) P hP (hdegree v) (hhalf v), ?_⟩
    unfold starWitnessCapacity
    split_ifs with hinactive
    · exact le_rfl
    · exact hupper v hinactive
  have hcoverage (v : V) : (G.degree v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) ≤
      2 * (copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    by_cases hinactive : inactiveStarTuple (q v)
    · simp only [starWitnessCapacity, ite_eq_left hinactive,
        div_self (by exact_mod_cast Nat.ne_of_gt hP : (P : ℝ) ≠ 0), Real.log_one, mul_zero, le_refl]
    have hlog : 0 ≤ Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ (by exact_mod_cast (hcapacity v).1 : (0 : ℝ) < starWitnessCapacity J P (q v))).mpr
      simpa only [one_mul] using (show (starWitnessCapacity J P (q v) : ℝ) ≤ P by exact_mod_cast (hcapacity v).2)
    have hcards : ((tupleGoodNeighbors G J f v (q v)).card : ℝ) ≤
        (copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card := by
      exact_mod_cast tupleGoodNeighbors_edges_card_le G H J f v (q v) hinactive
    exact mul_le_mul_of_nonneg_right ((hhalf v).trans (by linarith only [hcards])) hlog
  exact copy_star_deficit_of_witnesses G H J f s P L q
    (fun v => starWitnessTuples_of_dense_slots G H J hJ f v (q v) ε hε (hdegree v) (hlarge v))
    hcapacity hcoverage hdeficit

end Erdos911
