import Erdos911.DenseTupleWitnesses
import Erdos911.FractionalStarPatterns

namespace Erdos911

noncomputable def subsetSlotNeighbors {V W : Type*} (N : Finset V) (J : SimpleGraph W)
    (f : V → W) (q : Option W) : Finset V := by
  classical
  exact N.filter (fun u => ∀ w, q = some w → J.Adj w (f u))

theorem mem_subsetSlotNeighbors {V W : Type*} (N : Finset V) (J : SimpleGraph W)
    (f : V → W) (q : Option W) (u : V) :
    u ∈ subsetSlotNeighbors N J f q ↔ u ∈ N ∧ ∀ w, q = some w → J.Adj w (f u) := by
  classical
  exact Finset.mem_filter

theorem subset_tuple_half_coverage {V W : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (J : SimpleGraph W)
    (f : V → W) (v : V) (N : Finset V) (hN : N ⊆ F.neighborFinset v)
    (s : ℕ) (q : Fin s → Option W) (ε : ℝ)
    (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hslot : ∀ i, (1 - ε) * N.card ≤ (subsetSlotNeighbors N J f (q i)).card) :
    (N.card : ℝ) ≤ 2 * (tupleGoodNeighbors F J f v q).card := by
  classical
  let p := fun (i : Fin s) (u : V) => ∀ w, q i = some w → J.Adj w (f u)
  let : DecidableRel p := fun _ _ => Classical.propDecidable _
  have hslot' (i : Fin s) : (1 - ε) * N.card ≤ (N.filter (p i)).card := by
    have heq : subsetSlotNeighbors N J f (q i) = N.filter (p i) := by
      ext u
      simp only [mem_subsetSlotNeighbors, Finset.mem_filter, p]
    simpa only [heq] using hslot i
  have h := common_filter_half_card N p ε (by simpa only [Fintype.card_fin] using hbudget) hslot'
  let : DecidablePred (fun u => ∀ i : Fin s, p i u) := fun _ => Fintype.decidableForallFintype
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro u hu
  obtain ⟨huN, huAll⟩ := Finset.mem_filter.mp hu
  exact (mem_tupleGoodNeighbors F J f v u q).mpr
    ⟨(F.mem_neighborFinset v u).mp (hN huN), huAll⟩

theorem subset_starWitnessTuples_of_dense_slots {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (f : F.Copy H)
    (v : V) (N : Finset V) (hN : N ⊆ F.neighborFinset v) (hNpos : N.Nonempty)
    (s : ℕ) (q : Fin s → Option W) (ε : ℝ) (hε : ε < 1)
    (hslot : ∀ i, (1 - ε) * N.card ≤ (subsetSlotNeighbors N J f (q i)).card) :
    q ∈ starWitnessTuples H (f v) s := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  cases hqi : q i with
  | none =>
    rw [optionalTwoStepNeighbors]
    exact Finset.mem_insert_self _ _
  | some x =>
    have hpositive : (0 : ℝ) < (1 - ε) * N.card :=
      mul_pos (by linarith) (by exact_mod_cast hNpos.card_pos)
    have hhit : (subsetSlotNeighbors N J f (q i)).Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast hpositive.trans_le (hslot i)
    obtain ⟨u, hu⟩ := hhit
    obtain ⟨huN, huJ⟩ := (mem_subsetSlotNeighbors N J f (q i) u).mp hu
    have hnear : x ∈ twoStepNeighbors H (f v) := by
      apply (mem_twoStepNeighbors H (f v) x).mpr
      exact ⟨f u, map_rel f.toHom ((F.mem_neighborFinset v u).mp (hN huN)), (hJ (huJ x hqi)).symm⟩
    rw [optionalTwoStepNeighbors]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hnear, rfl⟩)

theorem subset_tuple_star_capacity_pos {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (J : SimpleGraph W) [DecidableRel J.Adj]
    (f : V → W) (v : V) (N : Finset V) (hN : N ⊆ F.neighborFinset v) (hNpos : N.Nonempty)
    (s P : ℕ) (hP : 0 < P) (q : Fin s → Option W) (ε : ℝ)
    (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hslot : ∀ i, (1 - ε) * N.card ≤ (subsetSlotNeighbors N J f (q i)).card) :
    0 < starWitnessCapacity J P q := by
  classical
  have hhalf := subset_tuple_half_coverage F J f v N hN s q ε hbudget hslot
  have hpositive : (tupleGoodNeighbors F J f v q).Nonempty := by
    apply Finset.card_pos.mp
    have hNposR : (0 : ℝ) < N.card := by exact_mod_cast hNpos.card_pos
    have hpos : (0 : ℝ) < (tupleGoodNeighbors F J f v q).card := by linarith only [hhalf, hNposR]
    exact_mod_cast hpos
  unfold starWitnessCapacity
  split_ifs
  · exact hP
  · obtain ⟨u, hu⟩ := hpositive
    exact Finset.card_pos.mpr ⟨f u, tupleGoodNeighbors_common_mem F J f v u q hu⟩

/-- Quarter-degree high-neighbor subsets yield `d/8` restricted edges
for an active tuple, with no half-of-full-degree assumption. -/
theorem subset_tuple_star_edge_mass {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W) [DecidableRel J.Adj]
    (f : F.Copy H) (v : V) (N : Finset V) (hN : N ⊆ F.neighborFinset v)
    (d s : ℕ) (hlarge : (d : ℝ) ≤ 4 * N.card) (q : Fin s → Option W)
    (hactive : ¬inactiveStarTuple q) (ε : ℝ) (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hslot : ∀ i, (1 - ε) * N.card ≤ (subsetSlotNeighbors N J f (q i)).card) :
    (d : ℝ) ≤ 8 * (copyRawEdges f ∩ starWitnessEdges J (f v) q).card := by
  have hhalf := subset_tuple_half_coverage F J f v N hN s q ε hbudget hslot
  have hmass : ((tupleGoodNeighbors F J f v q).card : ℝ) ≤
      (copyRawEdges f ∩ starWitnessEdges J (f v) q).card := by
    exact_mod_cast tupleGoodNeighbors_edges_card_le F H J f v q hactive
  linarith only [hlarge, hhalf, hmass]

end Erdos911
