import Erdos911.DictionaryEdgeColoring
import Erdos911.CheapPatternCopy
import Erdos911.RowCoordinateParameters

namespace Erdos911

noncomputable def copyRowCoordinate {A R V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : A ⊕ R → V) (q : ℕ)
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (y : R) : Fin (dictionaryWordLength q) :=
  if h : K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q then
    f ⟨g (Sum.inr y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ else 0

theorem copyRowCoordinate_of_low {A R V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : A ⊕ R → V) (q : ℕ)
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (y : R) (h : K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q) :
    copyRowCoordinate K g q f y = f ⟨g (Sum.inr y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ := by
  simp only [copyRowCoordinate, dite_eq_left h]

/-- A monochromatic copy makes every surviving pattern uniform at the
coordinate assigned to its low right image. -/
theorem monochromatic_surviving_row_uniform {A R V : Type*}
    [Fintype A] [DecidableEq A] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] (N : R → Finset A)
    (K : SimpleGraph V) [DecidableRel K.Adj] (g : (incidenceGraph N).Copy K) (q : ℕ)
    (c : V → Fin (dictionaryLabelCount q))
    (f : ↥(dictionaryLowVertices K (dictionaryLowDegree q)) → Fin (dictionaryWordLength q))
    (ω : (Fin (dictionaryLabelCount q) × Fin (dictionaryWordLength q)) → Bool) (b : Bool)
    (hmono : ∀ y x, x ∈ N y → dictionaryEdgeColor K q c f ω s(g (Sum.inl x), g (Sum.inr y)) = b)
    (y : R) (hy : y ∈ cheapBlockSurvivingRows N K g q) :
    ω ∈ dictionaryUniformRow ((targetTruncatedRows N (dictionaryLowDegree q) y).image
      (fun x => c (g (Sum.inl x)))) (copyRowCoordinate K g q f y) := by
  classical
  have hy' := (mem_survivingPatternRows _ _ _ _ _ y).mp hy
  have hlo : K.degree (g (Sum.inr y)) ≤ dictionaryLowDegree q := hy'.2.1
  refine ⟨b, ?_⟩
  intro l hl
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hl
  have hxhi : dictionaryLowDegree q < K.degree (g (Sum.inl x)) :=
    ((mem_targetHighLeft N _ x).mp (Finset.mem_inter.mp hx).2).trans_le
      (incidence_column_le_copy_degree N K g x)
  have hm := hmono y x (targetTruncatedRows_subset N _ y hx)
  rw [dictionaryEdgeColor_high_low K q c f ω _ _ hxhi hlo] at hm
  rw [copyRowCoordinate_of_low K g q f y hlo]
  exact hm

end Erdos911
