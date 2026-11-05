import Erdos911.NeighborhoodTupleBlocks
import Erdos911.ResidualPairGraph

namespace Erdos911

noncomputable def confinedNeighborhoodTuples {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X U A : Finset W) (t : ℕ) : Finset (Fin t → W) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin t => U)).filter
    (fun z => neighborhoodTupleBlock H X z ⊆ A)

theorem mem_confinedNeighborhoodTuples {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X U A : Finset W) (t : ℕ) (z : Fin t → W) :
    z ∈ confinedNeighborhoodTuples H X U A t ↔
      (∀ i, z i ∈ U) ∧ neighborhoodTupleBlock H X z ⊆ A := by
  classical
  simp only [confinedNeighborhoodTuples, Finset.mem_filter, Fintype.mem_piFinset]

/-- Only vertices within two steps of the distinguished candidate can
make a center tuple's block leave the allowed support. -/
theorem unconfinedNeighborhoodTuples_card {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X U A : Finset W) (t D : ℕ)
    (ht : 0 < t) (x : W) (hU : ∀ u ∈ U, H.Adj x u)
    (hD : ∀ w, H.degree w ≤ D) (T : ℝ) (hT : 0 ≤ T)
    (hcodegree : ∀ y ∈ X, y ∉ A → ((U ∩ H.neighborFinset y).card : ℝ) ≤ T) :
    (((Fintype.piFinset (fun _ : Fin t => U)) \
        confinedNeighborhoodTuples H X U A t).card : ℝ) ≤ (D : ℝ) ^ 2 * T ^ t := by
  classical
  let P := (twoStepNeighbors H x ∩ X) \ A
  let E (y : W) := (Fintype.piFinset (fun _ : Fin t => U)).filter
    (fun z => ∀ i, H.Adj y (z i))
  have hsub : (Fintype.piFinset (fun _ : Fin t => U)) \
      confinedNeighborhoodTuples H X U A t ⊆ P.biUnion E := by
    intro z hz
    obtain ⟨hzU, hznot⟩ := Finset.mem_sdiff.mp hz
    have hzU' : ∀ i, z i ∈ U := Fintype.mem_piFinset.mp hzU
    have hnot : ¬neighborhoodTupleBlock H X z ⊆ A := by
      intro h
      exact hznot ((mem_confinedNeighborhoodTuples H X U A t z).mpr ⟨hzU', h⟩)
    obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hnot
    obtain ⟨hyX, hyall⟩ := (mem_neighborhoodTupleBlock H X z y).mp hy
    have hyP : y ∈ P := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_inter.mpr ⟨?_, hyX⟩, hyA⟩
      exact (mem_twoStepNeighbors H x y).mpr
        ⟨z ⟨0, ht⟩, hU _ (hzU' ⟨0, ht⟩), (hyall ⟨0, ht⟩).symm⟩
    exact Finset.mem_biUnion.mpr ⟨y, hyP, Finset.mem_filter.mpr ⟨hzU, hyall⟩⟩
  have hE : ∀ y ∈ P, ((E y).card : ℝ) ≤ T ^ t := by
    intro y hy
    have hyX : y ∈ X := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2
    have hyA : y ∉ A := (Finset.mem_sdiff.mp hy).2
    have heq : (E y).card = (U ∩ H.neighborFinset y).card ^ t := by
      have h := tuples_in_intersection_card U (H.neighborFinset y) t
      simpa only [E, SimpleGraph.mem_neighborFinset] using h
    rw [heq, Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hcodegree y hyX hyA) t
  have hP : (P.card : ℝ) ≤ (D : ℝ) ^ 2 := by
    have hPN : P ⊆ twoStepNeighbors H x := fun y hy =>
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).1
    exact_mod_cast (Finset.card_le_card hPN).trans (twoStepNeighbors_card_le H D hD x)
  calc
    _ ≤ ((P.biUnion E).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ y ∈ P, ((E y).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ P, T ^ t := Finset.sum_le_sum hE
    _ = (P.card : ℝ) * T ^ t := by simp
    _ ≤ (D : ℝ) ^ 2 * T ^ t := mul_le_mul_of_nonneg_right hP (pow_nonneg hT t)

theorem confinedNeighborhoodTuples_card_lower {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X U A : Finset W) (t D : ℕ)
    (ht : 0 < t) (x : W) (hU : ∀ u ∈ U, H.Adj x u)
    (hD : ∀ w, H.degree w ≤ D) (T : ℝ) (hT : 0 ≤ T)
    (hcodegree : ∀ y ∈ X, y ∉ A → ((U ∩ H.neighborFinset y).card : ℝ) ≤ T) :
    (U.card : ℝ) ^ t - (D : ℝ) ^ 2 * T ^ t ≤
      ((confinedNeighborhoodTuples H X U A t).card : ℝ) := by
  classical
  have hbad := unconfinedNeighborhoodTuples_card H X U A t D ht x hU hD T hT hcodegree
  have hsub : confinedNeighborhoodTuples H X U A t ⊆ Fintype.piFinset (fun _ : Fin t => U) :=
    Finset.filter_subset _ _
  have hpartition := Finset.card_sdiff_add_card_eq_card hsub
  rw [Fintype.card_piFinset_const] at hpartition
  have hreal : (((Fintype.piFinset (fun _ : Fin t => U)) \
      confinedNeighborhoodTuples H X U A t).card : ℝ) +
      ((confinedNeighborhoodTuples H X U A t).card : ℝ) = (U.card : ℝ) ^ t := by
    exact_mod_cast hpartition
  linarith

/-- The eligible tuple supply includes the distinguished candidate,
has controlled support, and retains at least half of all center tuples. -/
theorem confinedNeighborhoodTuples_supply {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X U A : Finset W) (t D q : ℕ)
    (ht : 0 < t) (x : W) (hx : x ∈ X) (hU : ∀ u ∈ U, H.Adj x u)
    (hD : ∀ w, H.degree w ≤ D) (T : ℝ) (hT : 0 ≤ T)
    (hcodegree : ∀ y ∈ X, y ∉ A → ((U ∩ H.neighborFinset y).card : ℝ) ≤ T)
    (hA : A.card ≤ q) (hgap : (D : ℝ) ^ 2 * T ^ t ≤ (U.card : ℝ) ^ t / 2) :
    (U.card : ℝ) ^ t / 2 ≤ ((confinedNeighborhoodTuples H X U A t).card : ℝ) ∧
      ∀ z ∈ confinedNeighborhoodTuples H X U A t,
        x ∈ neighborhoodTupleBlock H X z ∧ (neighborhoodTupleBlock H X z).card ≤ q := by
  have hcount := confinedNeighborhoodTuples_card_lower H X U A t D ht x hU hD T hT hcodegree
  refine ⟨by linarith, ?_⟩
  intro z hz
  obtain ⟨hzU, hzA⟩ := (mem_confinedNeighborhoodTuples H X U A t z).mp hz
  exact ⟨(mem_neighborhoodTupleBlock H X z x).mpr ⟨hx, fun i => hU _ (hzU i)⟩,
    (Finset.card_le_card hzA).trans hA⟩

/-- A sparse high-codegree graph provides many nonempty, bounded-size
intersection blocks, each covering nearly all of the current candidate set. -/
theorem highCodegreeTuple_supply {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X U Y : Finset W) (t D q : ℕ) (T δ : ℝ)
    [DecidableRel (highCodegreeGraph H T).Adj]
    (ht : 0 < t) (x : W) (hx : x ∈ X) (hYX : Y ⊆ X)
    (hU : ∀ u ∈ U, H.Adj x u) (hD : ∀ w, H.degree w ≤ D) (hT : 0 ≤ T)
    (hQ : (highCodegreeGraph H T).degree x < q)
    (hgap : (D : ℝ) ^ 2 * T ^ t ≤ (U.card : ℝ) ^ t / 2)
    (hmiss : ∀ u ∈ U, ((Y.filter (fun y => ¬H.Adj y u)).card : ℝ) ≤ δ * Y.card) :
    let A := insert x (neighbors (highCodegreeGraph H T) x)
    (U.card : ℝ) ^ t / 2 ≤ ((confinedNeighborhoodTuples H X U A t).card : ℝ) ∧
      ∀ z ∈ confinedNeighborhoodTuples H X U A t,
        0 < (neighborhoodTupleBlock H X z).card ∧ (neighborhoodTupleBlock H X z).card ≤ q ∧
        (1 - t * δ) * Y.card ≤ ((Y ∩ neighborhoodTupleBlock H X z).card : ℝ) := by
  classical
  dsimp only
  let Q := highCodegreeGraph H T
  let A := insert x (neighbors Q x)
  have hcodegree : ∀ y ∈ X, y ∉ A → ((U ∩ H.neighborFinset y).card : ℝ) ≤ T := by
    intro y _ hyA
    have hxy : x ≠ y := by
      intro h
      apply hyA
      simp only [A, ← h, Finset.mem_insert_self]
    have hnot : ¬Q.Adj x y := by
      intro h
      apply hyA
      apply Finset.mem_insert.mpr
      right
      simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using h
    have hcodes : ((neighbors H x ∩ neighbors H y).card : ℝ) ≤ T := by
      apply le_of_not_gt
      intro h
      exact hnot ((highCodegreeGraph_adj H T x y).mpr ⟨hxy, h⟩)
    have hsub : U ∩ H.neighborFinset y ⊆ neighbors H x ∩ neighbors H y := by
      intro u hu
      obtain ⟨huU, huy⟩ := Finset.mem_inter.mp hu
      apply Finset.mem_inter.mpr
      constructor
      · simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using hU u huU
      · simpa only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] using
          (H.mem_neighborFinset y u).mp huy
    have hcard : ((U ∩ H.neighborFinset y).card : ℝ) ≤
        (neighbors H x ∩ neighbors H y).card := by exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans hcodes
  have hA : A.card ≤ q := by
    have heq : neighbors Q x = Q.neighborFinset x := by
      ext y
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    have h := Finset.card_insert_le x (neighbors Q x)
    rw [heq, Q.card_neighborFinset_eq_degree] at h
    have hQ' : Q.degree x < q := hQ
    change (insert x (neighbors Q x)).card ≤ q
    rw [heq]
    omega
  obtain ⟨hcount, hblocks⟩ := confinedNeighborhoodTuples_supply H X U A t D q ht x hx hU hD T hT
    hcodegree hA hgap
  refine ⟨hcount, ?_⟩
  intro z hz
  obtain ⟨hxB, hB⟩ := hblocks z hz
  refine ⟨Finset.card_pos.mpr ⟨x, hxB⟩, hB, ?_⟩
  exact neighborhoodTupleBlock_coverage H X Y z hYX δ (fun i =>
    hmiss (z i) (((mem_confinedNeighborhoodTuples H X U A t z).mp hz).1 i))

end Erdos911
