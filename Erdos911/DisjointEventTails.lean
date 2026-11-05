import Erdos911.ProductCoordinates
import Erdos911.BinomialMarkTail
import Erdos911.FiniteEventMarkov

open MeasureTheory ProbabilityTheory

namespace Erdos911

/-- Events supported on disjoint coordinate sets have the expected
finite-intersection probability under a product measure. -/
theorem disjoint_coordinate_events_inter {ι I : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq I]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSingletonClass (β i)]
    (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : I → Set (∀ i, β i)) (D : I → Finset ι)
    (hA : ∀ j, DependsOnlyOn (A j) (D j))
    (hdis : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (T : Finset I) :
    (Measure.pi μ).real (⋂ j ∈ T, A j) = ∏ j ∈ T, (Measure.pi μ).real (A j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    have hind := independent_of_disjoint_coordinate_events μ A D hA (A i) (D i) (hA i)
      (T : Set I) (fun j hj => hdis i j (by intro h; subst j; exact hi hj))
    have hmeasA : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i) :=
      MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
    have hmeasT : MeasurableSet[MeasurableSpace.generateFrom {s | ∃ j ∈ (T : Set I), s = A j}]
        (⋂ j ∈ T, A j) := by
      apply Finset.measurableSet_biInter
      intro j hj
      exact MeasurableSpace.measurableSet_generateFrom ⟨j, hj, rfl⟩
    have hmul := (Indep_iff _ _ (Measure.pi μ)).mp hind (A i) (⋂ j ∈ T, A j) hmeasA hmeasT
    have heq : (⋂ j ∈ insert i T, A j) = A i ∩ ⋂ j ∈ T, A j := by ext ω; simp
    rw [heq, Finset.prod_insert hi]
    rw [show (Measure.pi μ).real (A i ∩ ⋂ j ∈ T, A j) =
      (Measure.pi μ).real (A i) * (Measure.pi μ).real (⋂ j ∈ T, A j) by
        simp only [Measure.real, hmul, ENNReal.toReal_mul]]
    rw [ih]

/-- The subset union bound gives a binomial upper tail for events on
disjoint coordinates; the individual events need not be single bits. -/
theorem disjoint_coordinate_events_tail {ι I : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq I]
    {β : ι → Type*} [∀ i, Fintype (β i)] [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSingletonClass (β i)]
    (μ : ∀ i, Measure (β i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : I → Set (∀ i, β i)) (D : I → Finset ι)
    (hA : ∀ j, DependsOnlyOn (A j) (D j))
    (hdis : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (S : Finset I) (t : ℕ) (p : ℝ) (_hp : 0 ≤ p)
    (hprob : ∀ i ∈ S, (Measure.pi μ).real (A i) ≤ p) :
    (Measure.pi μ).real {ω | t ≤ (eventHitSet A S ω).card} ≤
      (S.card.choose t : ℝ) * p ^ t := by
  classical
  let B (T : ↥(S.powersetCard t)) : Set (∀ i, β i) := ⋂ j ∈ T.val, A j
  have hcover : {ω | t ≤ (S.filter (fun i => ω ∈ A i)).card} ⊆ ⋃ T, B T := by
    intro ω hω
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hω
    have hTS : T ⊆ S := hT.trans (Finset.filter_subset _ _)
    refine Set.mem_iUnion.mpr ⟨⟨T, Finset.mem_powersetCard.mpr ⟨hTS, hcard⟩⟩, ?_⟩
    simp only [B, Set.mem_iInter]
    intro j hj
    exact (Finset.mem_filter.mp (hT hj)).2
  have hbound (T : ↥(S.powersetCard t)) : (Measure.pi μ).real (B T) ≤ p ^ t := by
    change (Measure.pi μ).real (⋂ j ∈ T.val, A j) ≤ p ^ t
    rw [disjoint_coordinate_events_inter μ A D hA hdis]
    have hTS := (Finset.mem_powersetCard.mp T.property).1
    have hc := (Finset.mem_powersetCard.mp T.property).2
    calc
      _ ≤ ∏ _j ∈ T.val, p := Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg)
        (fun j hj => hprob j (hTS hj))
      _ = p ^ t := by simp only [Finset.prod_const, hc]
  have hsum := Finset.sum_le_sum (fun T (_ : T ∈ (Finset.univ : Finset ↥(S.powersetCard t))) => hbound T)
  have htotal : (∑ T : ↥(S.powersetCard t), p ^ t) = (S.card.choose t : ℝ) * p ^ t := by simp
  exact ((measureReal_mono hcover).trans (measureReal_iUnion_fintype_le B)).trans (hsum.trans_eq htotal)

end Erdos911
