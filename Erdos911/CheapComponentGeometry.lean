import Erdos911.CheapPatternCopy
import Erdos911.PatternComponentImages
import Erdos911.DictionaryScaleFromMass

namespace Erdos911

/-- Every vertex of a component that contains a surviving pattern has
the common degree scale needed by the row-assignment theorem. -/
theorem cheap_component_degree_lower {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N : R → Finset A)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K) (q : ℕ)
    (c : (patternCliqueGraph (targetTruncatedRows N (dictionaryLowDegree q))
      (cheapBlockSurvivingRows N K g q)).ConnectedComponent)
    (y : R) (hy : y ∈ cheapBlockSurvivingRows N K g q)
    (hne : (targetTruncatedRows N (dictionaryLowDegree q) y).Nonempty)
    (hc : ∀ x ∈ targetTruncatedRows N (dictionaryLowDegree q) y, x ∈ c.supp) :
    ∀ x ∈ c.supp, Fintype.card R ≤ 8 * dictionaryPatternCount q * K.degree (g (Sum.inl x)) := by
  classical
  let T := targetTruncatedRows N (dictionaryLowDegree q)
  let U := cheapBlockSurvivingRows N K g q
  let B := substantialTargetRows T (dictionaryRowMinimum q)
  let Low := fun y => K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q
  obtain ⟨x₀, hx₀⟩ := hne
  intro x hx
  obtain ⟨z, hz, hxz⟩ := patternCliqueGraph_covered_component T U x₀ x
    ⟨y, hy, hx₀⟩ (c.reachable_of_mem_supp (hc x₀ hx₀) hx)
  have hz' := (mem_survivingPatternRows B T Low (Fintype.card R) (dictionaryPatternCount q) z).mp hz
  exact hz'.2.2.1.trans (Nat.mul_le_mul_left (8 * dictionaryPatternCount q)
    (incidence_pattern_fiber_le_copy_degree N T (targetTruncatedRows_subset N _) K g B z x hxz))

theorem cheap_component_image_admissible {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N : R → Finset A)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K)
    (q : ℕ) (hq : 0 < q) (hA : Fintype.card A ≤ dictionaryLeftSize q)
    (hR : 128 * q ^ 69 ≤ Fintype.card R)
    (hcheap : (∑ v : A ⊕ R, K.degree (g v)) ≤ dictionaryDegreeCharge q * Fintype.card R)
    (c : (patternCliqueGraph (targetTruncatedRows N (dictionaryLowDegree q))
      (cheapBlockSurvivingRows N K g q)).ConnectedComponent)
    (y : R) (hy : y ∈ cheapBlockSurvivingRows N K g q)
    (hne : (targetTruncatedRows N (dictionaryLowDegree q) y).Nonempty)
    (hc : ∀ x ∈ targetTruncatedRows N (dictionaryLowDegree q) y, x ∈ c.supp) :
    let P := patternCliqueGraph (targetTruncatedRows N (dictionaryLowDegree q)) (cheapBlockSurvivingRows N K g q)
    let W := componentImage P (fun x => g (Sum.inl x)) c
    W ∈ smallConnectedSets (concreteDictionaryGraph K q) (dictionaryLeftSize q) ∧
      AdmissibleDictionaryScale K q W (Nat.log 2 (Fintype.card R)) := by
  classical
  let P := patternCliqueGraph (targetTruncatedRows N (dictionaryLowDegree q)) (cheapBlockSurvivingRows N K g q)
  let W := componentImage P (fun x => g (Sum.inl x)) c
  have hWcard : W.card ≤ dictionaryLeftSize q := (componentImage_card_le P _ c).trans hA
  have hWconn : ((concreteDictionaryGraph K q).induce (W : Set V)).Connected :=
    componentImage_connected P _ (cheapPatternCopy N K g q hq hcheap) c
  have hWpos : 0 < W.card := by
    obtain ⟨x, hx⟩ := c.nonempty_supp
    exact Finset.card_pos.mpr ⟨g (Sum.inl x), (mem_componentImage P _ c _).mpr ⟨x, hx, rfl⟩⟩
  refine ⟨(mem_smallConnectedSets _ _ W).mpr ⟨hWpos, hWcard, hWconn⟩, ?_⟩
  apply dictionary_scale_from_mass K q (Fintype.card R) hq hR W
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := (mem_componentImage P _ c v).mp hv
    exact cheap_component_degree_lower N K g q c y hy hne hc x hx
  · intro v hv
    obtain ⟨x, _, rfl⟩ := (mem_componentImage P _ c v).mp hv
    have hΓ : 0 < dictionaryDegreeCharge q := by unfold dictionaryDegreeCharge; positivity
    exact (cheap_image_degree_bounds K g _ hΓ hcheap).1 (Sum.inl x)

end Erdos911
