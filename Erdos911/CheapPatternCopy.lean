import Erdos911.TargetPatternGraph
import Erdos911.DictionaryHostPairs

namespace Erdos911

theorem incidence_column_le_copy_degree {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N : R → Finset A)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K) (x : A) :
    (incidenceColumn N x).card ≤ K.degree (g (Sum.inl x)) := by
  have h := g.degree_le (Sum.inl x)
  simpa only [incidenceGraph_degree_left, incidenceColumn] using h

theorem incidence_pattern_fiber_le_copy_degree {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N T : R → Finset A) (hT : ∀ y, T y ⊆ N y)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K)
    (B : Finset R) (y : R) (x : A) (hx : x ∈ T y) :
    (patternFiber B T (T y)).card ≤ K.degree (g (Sum.inl x)) := by
  classical
  apply (Finset.card_le_card ?_).trans (incidence_column_le_copy_degree N K g x)
  intro z hz
  have heq := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT z (heq.symm ▸ hx)⟩

/-- A surviving repeated pattern becomes a clique in the host conflict graph. -/
theorem cheap_surviving_pattern_host_adj {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N : R → Finset A)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K)
    (q : ℕ) (hq : 0 < q) (hcheap : (∑ v : A ⊕ R, K.degree (g v)) ≤ dictionaryDegreeCharge q * Fintype.card R)
    (y : R) (hy : y ∈ cheapBlockSurvivingRows N K g q)
    (x z : A) (hne : x ≠ z)
    (hx : x ∈ targetTruncatedRows N (dictionaryLowDegree q) y)
    (hz : z ∈ targetTruncatedRows N (dictionaryLowDegree q) y) :
    (concreteDictionaryGraph K q).Adj (g (Sum.inl x)) (g (Sum.inl z)) := by
  classical
  let T := targetTruncatedRows N (dictionaryLowDegree q)
  let B := substantialTargetRows T (dictionaryRowMinimum q)
  let Low := fun y => K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q
  let F := patternFiber B T (T y)
  let Z := F.filter Low
  have hy' := (mem_survivingPatternRows B T Low (Fintype.card R) (dictionaryPatternCount q) y).mp hy
  have hmass : Fintype.card R ≤ 16 * dictionaryPatternCount q * Z.card := by
    have hh := Nat.mul_le_mul_left (8 * dictionaryPatternCount q) hy'.2.2.2
    change Fintype.card R ≤ 16 * dictionaryPatternCount q * Z.card
    nlinarith only [hy'.2.2.1, hh]
  have hΓ : 0 < dictionaryDegreeCharge q := by
    unfold dictionaryDegreeCharge
    positivity
  have hmax := (cheap_image_degree_bounds K g (dictionaryDegreeCharge q) hΓ hcheap).1
  let r : ↥Z → ↥(dictionaryLowVertices K (dictionaryLowDegree q)) := fun t =>
    ⟨g (Sum.inr t.val), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp t.property).2⟩⟩
  have hr : Function.Injective r := by
    intro u v h
    apply Subtype.ext
    apply Sum.inr_injective
    apply g.injective
    exact congrArg Subtype.val h
  refine dictionaryHostGraph_adj_of_shared_rows (R := ↥Z) K (dictionaryLowDegree q)
    (16 * (dictionaryPatternCount q : ℝ) * dictionaryDegreeCharge q)
    ((dictionaryDegreeCharge q : ℝ) * Fintype.card R) (by positivity)
    (g (Sum.inl x)) (g (Sum.inl z))
    (fun h => hne (Sum.inl_injective (g.injective h))) ?_ ?_ ?_ ?_
    (Finset.univ : Finset ↥Z) r hr ?_ ?_
  · exact ((mem_targetHighLeft N _ x).mp (Finset.mem_inter.mp hx).2).trans_le
      (incidence_column_le_copy_degree N K g x)
  · exact ((mem_targetHighLeft N _ z).mp (Finset.mem_inter.mp hz).2).trans_le
      (incidence_column_le_copy_degree N K g z)
  · exact_mod_cast hmax (Sum.inl x)
  · exact_mod_cast hmax (Sum.inl z)
  · intro t _
    have heq : T t.val = T y := (Finset.mem_filter.mp (Finset.mem_filter.mp t.property).1).2
    have hxt : x ∈ N t.val := targetTruncatedRows_subset N _ _ (show x ∈ T t.val by rw [heq]; exact hx)
    have hzt : z ∈ N t.val := targetTruncatedRows_subset N _ _ (show z ∈ T t.val by rw [heq]; exact hz)
    exact ⟨g.toHom.map_adj hxt, g.toHom.map_adj hzt⟩
  · simp only [Finset.card_univ, Fintype.card_coe]
    have hm : (Fintype.card R : ℝ) ≤ 16 * dictionaryPatternCount q * Z.card := by exact_mod_cast hmass
    nlinarith [Nat.cast_nonneg (α := ℝ) (dictionaryDegreeCharge q)]

noncomputable def cheapPatternCopy {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N : R → Finset A)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K)
    (q : ℕ) (hq : 0 < q) (hcheap : (∑ v : A ⊕ R, K.degree (g v)) ≤ dictionaryDegreeCharge q * Fintype.card R) :
    (patternCliqueGraph (targetTruncatedRows N (dictionaryLowDegree q))
      (cheapBlockSurvivingRows N K g q)).Copy (concreteDictionaryGraph K q) where
  toHom := {
    toFun := fun x => g (Sum.inl x)
    map_rel' := by
      intro x z h
      obtain ⟨hne, y, hy, hx, hz⟩ := h
      exact cheap_surviving_pattern_host_adj N K g q hq hcheap y hy x z hne hx hz }
  injective' := g.injective.comp Sum.inl_injective

end Erdos911
