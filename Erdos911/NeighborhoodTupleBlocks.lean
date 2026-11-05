import Erdos911.CandidateCenters
import Erdos911.StarWitnessCounting
import Erdos911.IncidenceAveraging

namespace Erdos911

/-- Ordered center tuples index the common-neighborhood marking variables.
Repeated centers are permitted. -/
noncomputable def neighborhoodTupleBlock {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) {t : ℕ} (z : Fin t → W) : Finset W := by
  classical
  exact X.filter (fun x => ∀ i, H.Adj x (z i))

theorem mem_neighborhoodTupleBlock {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) {t : ℕ} (z : Fin t → W) (x : W) :
    x ∈ neighborhoodTupleBlock H X z ↔ x ∈ X ∧ ∀ i, H.Adj x (z i) := by
  classical
  simp only [neighborhoodTupleBlock, Finset.mem_filter]

theorem neighborhoodTupleBlock_subset {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) (X : Finset W) {t : ℕ} (z : Fin t → W) :
    neighborhoodTupleBlock H X z ⊆ X := by
  classical
  exact Finset.filter_subset _ _

theorem tuples_in_intersection_card {W : Type*} [DecidableEq W]
    (U N : Finset W) (t : ℕ) :
    ((Fintype.piFinset (fun _ : Fin t => U)).filter (fun z => ∀ i, z i ∈ N)).card =
      (U ∩ N).card ^ t := by
  classical
  have heq : (Fintype.piFinset (fun _ : Fin t => U)).filter (fun z => ∀ i, z i ∈ N) =
      Fintype.piFinset (fun _ : Fin t => U ∩ N) := by
    ext z
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_inter]
    exact forall_and.symm
  rw [heq, Fintype.card_piFinset_const]

theorem neighborhoodTupleBlock_incidence {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X : Finset W) (t : ℕ)
    (x : W) (hx : x ∈ X) :
    ((Finset.univ : Finset (Fin t → W)).filter
      (fun z => x ∈ neighborhoodTupleBlock H X z)).card = H.degree x ^ t := by
  classical
  have heq : (Finset.univ : Finset (Fin t → W)).filter
      (fun z => x ∈ neighborhoodTupleBlock H X z) =
      Fintype.piFinset (fun _ : Fin t => H.neighborFinset x) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_neighborhoodTupleBlock, hx, Fintype.mem_piFinset, SimpleGraph.mem_neighborFinset]
  rw [heq, Fintype.card_piFinset_const, H.card_neighborFinset_eq_degree]

theorem neighborhoodTupleBlock_total_size {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X : Finset W) (t : ℕ) :
    (∑ z : Fin t → W, (neighborhoodTupleBlock H X z).card) = ∑ x ∈ X, H.degree x ^ t := by
  classical
  have heq (z : Fin t → W) : X.filter (fun x => x ∈ neighborhoodTupleBlock H X z) =
      neighborhoodTupleBlock H X z := by
    ext x
    simp only [Finset.mem_filter, mem_neighborhoodTupleBlock, and_self_left]
  have h := incidence_card_sum_comm Finset.univ X
    (fun z : Fin t → W => fun x => x ∈ neighborhoodTupleBlock H X z)
  simp_rw [heq] at h
  rw [h]
  exact Finset.sum_congr rfl (fun x hx => neighborhoodTupleBlock_incidence H X t x hx)

/-- The total size of any retained family of tuple blocks is bounded by
the number of eligible vertices times the maximum-degree power. -/
theorem neighborhoodTupleBlock_family_size {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X : Finset W) (t D : ℕ)
    (hD : ∀ x ∈ X, H.degree x ≤ D) (A : Finset (Fin t → W)) :
    (∑ z ∈ A, (neighborhoodTupleBlock H X z).card) ≤ X.card * D ^ t := by
  classical
  calc
    _ ≤ ∑ z : Fin t → W, (neighborhoodTupleBlock H X z).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = ∑ x ∈ X, H.degree x ^ t := neighborhoodTupleBlock_total_size H X t
    _ ≤ ∑ _x ∈ X, D ^ t := Finset.sum_le_sum (fun x hx => Nat.pow_le_pow_left (hD x hx) t)
    _ = X.card * D ^ t := by simp

/-- If every chosen center misses at most a fraction of a candidate set,
their common-neighborhood block misses at most the sum of those fractions. -/
theorem neighborhoodTupleBlock_coverage {W : Type*} [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (X Y : Finset W) {t : ℕ} (z : Fin t → W)
    (hYX : Y ⊆ X) (δ : ℝ)
    (hmiss : ∀ i, ((Y.filter (fun y => ¬H.Adj y (z i))).card : ℝ) ≤ δ * Y.card) :
    (1 - t * δ) * Y.card ≤ ((Y ∩ neighborhoodTupleBlock H X z).card : ℝ) := by
  classical
  have heq : Y \ neighborhoodTupleBlock H X z =
      Finset.univ.biUnion (fun i : Fin t => Y.filter (fun y => ¬H.Adj y (z i))) := by
    ext y
    simp only [Finset.mem_sdiff, mem_neighborhoodTupleBlock, Finset.mem_biUnion,
      Finset.mem_univ, Finset.mem_filter, true_and]
    constructor
    · rintro ⟨hy, hn⟩
      have hnall : ¬∀ i, H.Adj y (z i) := fun hall => hn ⟨hYX hy, hall⟩
      obtain ⟨i, hi⟩ := not_forall.mp hnall
      exact ⟨i, hy, hi⟩
    · rintro ⟨i, hy, hi⟩
      exact ⟨hy, fun h => hi (h.2 i)⟩
  have hsum : ((Y \ neighborhoodTupleBlock H X z).card : ℝ) ≤ (t : ℝ) * (δ * Y.card) := by
    rw [heq]
    calc
      _ ≤ ∑ i : Fin t, ((Y.filter (fun y => ¬H.Adj y (z i))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin t, δ * Y.card := Finset.sum_le_sum (fun i _ => hmiss i)
      _ = (t : ℝ) * (δ * Y.card) := by simp
  have hpartition : ((Y \ neighborhoodTupleBlock H X z).card : ℝ) +
      ((Y ∩ neighborhoodTupleBlock H X z).card : ℝ) = Y.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter Y (neighborhoodTupleBlock H X z)
  nlinarith only [hsum, hpartition]

end Erdos911
