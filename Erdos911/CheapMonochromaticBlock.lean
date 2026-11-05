import Erdos911.CheapComponentGeometry
import Erdos911.PatternRowPartition
import Erdos911.AssignedBadRows
import Erdos911.DictionaryCopyCoordinates
import Erdos911.DictionaryHitInjection
import Erdos911.DictionaryTestTransfer
import Erdos911.DictionaryRowAssignment
import Erdos911.PatternComponentMembership

namespace Erdos911

/-- The concrete dictionary coloring has no cheap monochromatic copy
of a dictionary-good large-right target block. -/
theorem no_cheap_monochromatic_block {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N : R → Finset A)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K)
    (q : ℕ) (hq : 2 ^ 32 ≤ q) (hrow : ∀ y, (N y).card = q)
    (hA : Fintype.card A ≤ dictionaryLeftSize q) (hR : 128 * q ^ 69 ≤ Fintype.card R)
    (c : V → Fin (dictionaryLabelCount q))
    (hc : ∀ W : Finset V, W.card ≤ dictionaryLeftSize q →
      ((concreteDictionaryGraph K q).induce (W : Set V)).Connected → Set.InjOn c (W : Set V))
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (hf : ∀ W ∈ smallConnectedSets (concreteDictionaryGraph K q) (dictionaryLeftSize q),
      ∀ j, AdmissibleDictionaryScale K q W j →
        ∀ S : Finset (Fin (dictionaryWordLength q)), S.card ≤ dictionaryBadLimit q →
          (eventHitSet (fun y => labelSubsetEvent y S) (dictionaryRowSupport K q W) f).card <
            dictionaryRowThreshold q (2 ^ j))
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool)
    (hgood : BlockDictionaryGood N q ω) (b : Bool)
    (hmono : ∀ y x, x ∈ N y → dictionaryEdgeColor K q c f ω s(g (Sum.inl x), g (Sum.inr y)) = b) :
    ¬ (∑ v : A ⊕ R, K.degree (g v)) ≤ dictionaryDegreeCharge q * Fintype.card R := by
  classical
  intro hcheap
  have hqpos : 0 < q := by norm_num at hq; omega
  have hqfour : 4 ≤ q := by norm_num at hq; omega
  have hspos : 0 < dictionaryRowMinimum q := by unfold dictionaryRowMinimum; omega
  have hbpos : 0 < Fintype.card R := (by positivity : 0 < 128 * q ^ 69).trans_le hR
  let T := targetTruncatedRows N (dictionaryLowDegree q)
  let B := substantialTargetRows T (dictionaryRowMinimum q)
  let U := cheapBlockSurvivingRows N K g q
  let P := patternCliqueGraph T U
  let : Fintype P.ConnectedComponent := Fintype.ofFinite _
  let Bc := patternComponentRows T B P
  let Nlabel := fun y => (T y).image (fun x => c (g (Sum.inl x)))
  let τ := copyRowCoordinate K g q f
  let Bad := fun d : P.ConnectedComponent => assignedBadRows Nlabel (Bc d) U τ ω
  have hUB : U ⊆ B := by
    intro y hy
    exact ((mem_survivingPatternRows _ _ _ _ _ y).mp hy).1
  have hnonempty (y : R) (hy : y ∈ B) : (T y).Nonempty := by
    apply Finset.card_pos.mp
    exact hspos.trans_le ((mem_substantialTargetRows _ _ y).mp hy)
  have hUmass : 3 * Fintype.card R ≤ 8 * U.card :=
    cheap_block_surviving_rows_large N K g q hqpos hrow hA hR hcheap
  have hpartition : (∑ d : P.ConnectedComponent, (U ∩ Bc d).card) = U.card :=
    patternComponentRows_partition T B U hUB hnonempty
  have hBmass : (∑ d : P.ConnectedComponent, (Bc d).card) ≤ Fintype.card R :=
    (patternComponentRows_sum_le T B P hnonempty).trans (Finset.card_le_univ B)
  have hUni (y : R) (hy : y ∈ U) : ω ∈ dictionaryUniformRow (Nlabel y) (τ y) :=
    monochromatic_surviving_row_uniform N K g q c f ω b hmono y hy
  have hbadmass : Fintype.card R ≤ 8 * (∑ d, (Bad d).card) :=
    assignedBadRows_count Nlabel Bc U τ ω hUni hpartition _ hBmass hUmass
  have hcomp : Fintype.card P.ConnectedComponent ≤ dictionaryLeftSize q :=
    (connectedComponent_count_le P).trans hA
  obtain ⟨d, hd⟩ := exists_large_assignedBadRows Bad (dictionaryLeftSize q) (Fintype.card R)
    hbpos hcomp hbadmass
  have hBadpos : 0 < (Bad d).card := by
    by_contra hn
    have hz : (Bad d).card = 0 := by omega
    rw [hz, mul_zero] at hd
    omega
  obtain ⟨y₀, hy₀⟩ := Finset.card_pos.mp hBadpos
  have hy₀split := Finset.mem_inter.mp (Finset.mem_filter.mp hy₀).1
  have hy₀U : y₀ ∈ U := hy₀split.1
  have hy₀B := (mem_patternComponentRows T B P d y₀).mp hy₀split.2
  have hy₀c : ∀ x ∈ T y₀, x ∈ d.supp := hy₀B.2
  let W := componentImage P (fun x => g (Sum.inl x)) d
  obtain ⟨hW, hj⟩ := cheap_component_image_admissible N K g q hqpos hA hR hcheap d
    y₀ hy₀U (hnonempty y₀ hy₀B.1) hy₀c
  have hWinj : Set.InjOn c (W : Set V) := hc W ((mem_smallConnectedSets _ _ _).mp hW).2.1
    ((mem_smallConnectedSets _ _ _).mp hW).2.2
  have hlabels : Set.InjOn (fun x : A => c (g (Sum.inl x))) (d.supp.toFinset : Set A) := by
    intro x hx z hz heq
    apply Sum.inl_injective
    apply g.injective
    apply hWinj
    · exact (mem_componentImage P _ d _).mpr ⟨x, Set.mem_toFinset.mp hx, rfl⟩
    · exact (mem_componentImage P _ d _).mpr ⟨z, Set.mem_toFinset.mp hz, rfl⟩
    · exact heq
  have hBceq : Bc d = B.filter (fun y => T y ⊆ d.supp.toFinset) := by
    ext y
    simp only [Bc, patternComponentRows, Finset.mem_filter, Finset.subset_iff, Set.mem_toFinset]
  have htest := block_dictionary_controls_subset N q ω hgood d.supp.toFinset
    (fun x => c (g (Sum.inl x))) hlabels
  dsimp only at htest
  change (eventHitSet (dictionaryBadCoordinate Nlabel
    (B.filter (fun y => T y ⊆ d.supp.toFinset))) Finset.univ ω).card < dictionaryBadLimit q at htest
  rw [← hBceq] at htest
  let S := eventHitSet (dictionaryBadCoordinate Nlabel (Bc d)) Finset.univ ω
  have hS : S.card ≤ dictionaryBadLimit q := htest.le
  have hhit := hf W hW (Nat.log 2 (Fintype.card R)) hj S hS
  have hlow (y : R) (hy : y ∈ Bad d) : K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q := by
    have hyU := (Finset.mem_inter.mp (Finset.mem_filter.mp hy).1).1
    exact ((mem_survivingPatternRows _ _ _ _ _ y).mp hyU).2.1
  have hsupport (y : R) (hy : y ∈ Bad d) : ∃ v ∈ W, K.Adj v (g (Sum.inr y)) := by
    have hyBc := (Finset.mem_inter.mp (Finset.mem_filter.mp hy).1).2
    obtain ⟨hyB, hyc⟩ := (mem_patternComponentRows T B P d y).mp hyBc
    obtain ⟨x, hx⟩ := hnonempty y hyB
    refine ⟨g (Sum.inl x), (mem_componentImage P _ d _).mpr ⟨x, hyc x hx, rfl⟩, ?_⟩
    exact g.toHom.map_adj (targetTruncatedRows_subset N _ y hx)
  have hcoord (y : R) (hy : y ∈ Bad d) :
      f ⟨g (Sum.inr y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlow y hy⟩⟩ ∈ S := by
    have hh := (Finset.mem_filter.mp hy).2
    have hm : τ y ∈ S := (mem_eventHitSet _ _ _ _).mpr ⟨Finset.mem_univ _, hh⟩
    simpa only [τ, copyRowCoordinate_of_low K g q f y (hlow y hy)] using hm
  have hinj : Set.InjOn (fun y : R => g (Sum.inr y)) (Bad d : Set R) := by
    intro y _ z _ heq
    exact Sum.inr_injective (g.injective heq)
  have hcount := injective_rows_le_dictionary_hits K q W f S (Bad d)
    (fun y => g (Sum.inr y)) hinj hlow hsupport hcoord
  have hscale : 2 ^ Nat.log 2 (Fintype.card R) ≤ 8 * dictionaryLeftSize q * (Bad d).card :=
    (Nat.pow_log_le_self 2 hbpos.ne').trans hd
  have hthreshold := dictionary_threshold_le_of_mass q (2 ^ Nat.log 2 (Fintype.card R)) (Bad d).card hqpos hscale
  exact (not_lt_of_ge (hthreshold.trans hcount)) hhit

end Erdos911
