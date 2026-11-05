import Erdos911.PartialLabelTests
import Erdos911.DependentDictionarySelection

namespace Erdos911

noncomputable def targetHighLeft {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (D : ℕ) : Finset A := by
  classical
  exact Finset.univ.filter (fun x => D < (incidenceColumn N x).card)

noncomputable def targetTruncatedRows {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (D : ℕ) (y : R) : Finset A := N y ∩ targetHighLeft N D

noncomputable def substantialTargetRows {A R : Type*} [Fintype R]
    (N : R → Finset A) (s : ℕ) : Finset R := by
  classical
  exact Finset.univ.filter (fun y => s ≤ (N y).card)

theorem mem_targetHighLeft {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (D : ℕ) (x : A) : x ∈ targetHighLeft N D ↔ D < (incidenceColumn N x).card := by
  classical
  simp [targetHighLeft]

theorem targetTruncatedRows_subset {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (D : ℕ) (y : R) : targetTruncatedRows N D y ⊆ N y := Finset.inter_subset_left

theorem mem_substantialTargetRows {A R : Type*} [Fintype R]
    (N : R → Finset A) (s : ℕ) (y : R) : y ∈ substantialTargetRows N s ↔ s ≤ (N y).card := by
  classical
  simp [substantialTargetRows]

noncomputable def blockTestNeighborhoods {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (q : ℕ) (f : A → Option (Fin (dictionaryLabelCount q))) (y : R) :=
  partialLabelRange f (targetTruncatedRows N (dictionaryLowDegree q) y)

noncomputable def blockTestRows {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (q : ℕ) (f : A → Option (Fin (dictionaryLabelCount q))) :=
  partialLabelTestRows (targetTruncatedRows N (dictionaryLowDegree q))
    (substantialTargetRows (targetTruncatedRows N (dictionaryLowDegree q)) (dictionaryRowMinimum q)) f

abbrev BlockDictionaryGood {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    (N : R → Finset A) (q : ℕ)
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool) : Prop :=
  ∀ f : A → Option (Fin (dictionaryLabelCount q)),
    (eventHitSet (dictionaryBadCoordinate (blockTestNeighborhoods N q f) (blockTestRows N q f))
      Finset.univ ω).card < dictionaryBadLimit q

theorem blockTestRows_minimum {A R : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    (N : R → Finset A) (q : ℕ) (f : A → Option (Fin (dictionaryLabelCount q))) (y : R)
    (hy : y ∈ blockTestRows N q f) : dictionaryRowMinimum q ≤ (blockTestNeighborhoods N q f y).card := by
  apply partialLabelTestRows_minimum (targetTruncatedRows N (dictionaryLowDegree q)) _ f _ ?_ y hy
  intro z hz
  exact (mem_substantialTargetRows _ _ z).mp hz

/-- All concrete partial-map tests for all target incidence blocks can
be covered by one dictionary. No uniform right-vertex type is required. -/
theorem exists_target_block_dictionary {I : Type*} [Fintype I]
    (A R : I → Type*) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    (N : ∀ i, R i → Finset (A i)) (q : ℕ) (hq : 65536 ≤ q)
    (hA : ∀ i, Fintype.card (A i) ≤ dictionaryLeftSize q) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool,
      (7 / 8 : ℝ) * (∑ i : I, w i) ≤ ∑ i : I, if BlockDictionaryGood (N i) q ω then w i else 0 := by
  let T := fun i => A i → Option (Fin (dictionaryLabelCount q))
  obtain ⟨ω, hω⟩ := exists_dependent_dictionary q hq R T
    (fun i f => blockTestNeighborhoods (N i) q f) (fun i f => blockTestRows (N i) q f)
    (fun i f y hy => blockTestRows_minimum (N i) q f y hy)
    (fun i => dictionary_partial_map_count q (A i) (hA i)) w hw
  exact ⟨ω, hω⟩

end Erdos911
