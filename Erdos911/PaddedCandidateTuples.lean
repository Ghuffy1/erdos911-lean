import Erdos911.DenseTupleWitnesses
import Erdos911.NeighborhoodTupleMarking

namespace Erdos911

/-- Enumerate a finite candidate set in the initial slots and leave the
remaining witness slots inactive. -/
noncomputable def paddedCandidateTuple {W : Type*} (U : Finset W) (s : ℕ) : Fin s → Option W :=
  fun i => if h : i.val < U.card then some ((U.equivFin.symm ⟨i.val, h⟩).val) else none

theorem paddedCandidateTuple_mem {W : Type*} (U : Finset W) (s : ℕ)
    (i : Fin s) (x : W) (hi : paddedCandidateTuple U s i = some x) : x ∈ U := by
  classical
  unfold paddedCandidateTuple at hi
  split_ifs at hi with h
  · have hx : (U.equivFin.symm ⟨i.val, h⟩).val = x := Option.some.inj hi
    exact hx ▸ (U.equivFin.symm ⟨i.val, h⟩).property

theorem paddedCandidateTuple_surjective {W : Type*} (U : Finset W) (s : ℕ)
    (hsize : U.card ≤ s) (x : W) (hx : x ∈ U) :
    ∃ i : Fin s, paddedCandidateTuple U s i = some x := by
  classical
  let j := U.equivFin ⟨x, hx⟩
  let i : Fin s := ⟨j.val, j.isLt.trans_le hsize⟩
  refine ⟨i, ?_⟩
  dsimp only [paddedCandidateTuple, i]
  rw [dite_eq_left j.isLt]
  change some (U.equivFin.symm j).val = some x
  exact congrArg (fun z : U => some z.val) (U.equivFin.symm_apply_apply ⟨x, hx⟩)

theorem paddedCandidateTuple_active {W : Type*} (U : Finset W) (s : ℕ)
    (hsize : U.card ≤ s) (hU : U.Nonempty) : ¬inactiveStarTuple (paddedCandidateTuple U s) := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨i, hi⟩ := paddedCandidateTuple_surjective U s hsize x hx
  intro hn
  have hnone := hn i
  rw [hi] at hnone
  cases hnone

theorem tupleCommonNeighbors_paddedCandidateTuple {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (U : Finset W) (s : ℕ) (hsize : U.card ≤ s) :
    tupleCommonNeighbors J (paddedCandidateTuple U s) = commonCenters J.Adj U := by
  classical
  ext z
  rw [mem_commonCenters_iff]
  change (z ∈ Finset.univ.filter (fun z => ∀ i x, paddedCandidateTuple U s i = some x → J.Adj x z)) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h x hx
    obtain ⟨i, hi⟩ := paddedCandidateTuple_surjective U s hsize x hx
    exact h i x hi
  · intro h i x hi
    exact h x (paddedCandidateTuple_mem U s i x hi)

end Erdos911
