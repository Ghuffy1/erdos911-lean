import Erdos911.UniformLabels
import Erdos911.ProductCoordinates
import Mathlib.Data.Fintype.EquivFin

open MeasureTheory

namespace Erdos911

def labelPattern {V A : Type*} (S : Finset V) (b : V → A) : Set (V → A) :=
  {f | ∀ v ∈ S, f v = b v}

theorem uniformLabelMeasure_pattern {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (S : Finset V) (b : V → A) :
    (uniformLabelMeasure V A).real (labelPattern S b) =
      (1 / (Fintype.card A : ℝ)) ^ S.card := by
  classical
  have hset : labelPattern S b = Set.univ.pi
      (fun v => if v ∈ S then ({b v} : Set A) else Set.univ) := by
    ext f
    simp only [labelPattern, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · simpa only [ite_eq_left hv, Set.mem_singleton_iff] using h v hv
      · simp only [ite_eq_right hv, Set.mem_univ]
    · intro h v hv
      simpa only [ite_eq_left hv, Set.mem_singleton_iff] using h v
  have hm (a : A) : ((PMF.uniformOfFintype A).toMeasure {a}).toReal =
      1 / (Fintype.card A : ℝ) := by
    rw [PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a), PMF.uniformOfFintype_apply]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  calc
    _ = ∏ v : V, ((PMF.uniformOfFintype A).toMeasure
        (if v ∈ S then ({b v} : Set A) else Set.univ)).toReal := by
      simp only [Measure.real, uniformLabelMeasure, hset, Measure.pi_pi, ENNReal.toReal_prod]
    _ = ∏ v : V, if v ∈ S then 1 / (Fintype.card A : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ S
      · simp only [ite_eq_left hv, hm]
      · simp only [ite_eq_right hv, measure_univ, ENNReal.toReal_one]
    _ = _ := by rw [Finset.prod_ite_mem_eq]; simp only [Finset.prod_const]

/-- Restriction to distinct coordinates preserves independent uniform labels. -/
theorem uniformLabelMeasure_map_injective {V I A : Type*}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (e : I → V) (he : Function.Injective e) :
    (uniformLabelMeasure V A).map (fun f i => f (e i)) = uniformLabelMeasure I A := by
  classical
  have hmeas : Measurable (fun (f : V → A) (i : I) => f (e i)) := by fun_prop
  apply Measure.ext_of_measureReal_singleton
  intro g
  let b : V → A := Function.extend e g (fun _ => Classical.choice ‹Nonempty A›)
  let S := Finset.univ.image e
  have hb (i : I) : b (e i) = g i := he.extend_apply g _ i
  have hset : (fun (f : V → A) i => f (e i)) ⁻¹' {g} = labelPattern S b := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, labelPattern, Set.mem_ofPred_eq]
    constructor
    · intro h v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      exact (congrFun h i).trans (hb i).symm
    · intro h
      funext i
      exact (h (e i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).trans (hb i)
  have hcard : S.card = Fintype.card I := by
    rw [Finset.card_image_of_injective _ he, Finset.card_univ]
  rw [Measure.real, Measure.map_apply hmeas (measurableSet_singleton g)]
  change (uniformLabelMeasure V A).real _ = _
  rw [hset, uniformLabelMeasure_pattern, hcard, uniformLabelMeasure_singleton]

noncomputable def setLabelEmbedding {V : Type*} (S : Finset V) : Fin S.card → V :=
  fun i => (S.equivFin.symm i).val

theorem setLabelEmbedding_mem {V : Type*} (S : Finset V) (i : Fin S.card) :
    setLabelEmbedding S i ∈ S := (S.equivFin.symm i).property

theorem setLabelEmbedding_injective {V : Type*} (S : Finset V) :
    Function.Injective (setLabelEmbedding S) := by
  intro i j h
  exact S.equivFin.symm.injective (Subtype.ext h)

noncomputable def orderedSetLabels {V A : Type*} (S : Finset V) (f : V → A) : Fin S.card → A :=
  fun i => f (setLabelEmbedding S i)

theorem orderedSetLabels_eq_of_agree {V A : Type*} (S : Finset V) (f g : V → A)
    (h : ∀ v ∈ S, f v = g v) : orderedSetLabels S f = orderedSetLabels S g := by
  funext i
  exact h (setLabelEmbedding S i) (setLabelEmbedding_mem S i)

theorem uniformLabelMeasure_orderedSetLabels {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (S : Finset V)
    (E : Set (Fin S.card → A)) :
    (uniformLabelMeasure V A).real (orderedSetLabels S ⁻¹' E) =
      (uniformLabelMeasure (Fin S.card) A).real E := by
  have hmeas : Measurable (orderedSetLabels S : (V → A) → (Fin S.card → A)) := by fun_prop [orderedSetLabels]
  have h := uniformLabelMeasure_map_injective (A := A) (setLabelEmbedding S) (setLabelEmbedding_injective S)
  rw [← h]
  change (uniformLabelMeasure V A).real (orderedSetLabels S ⁻¹' E) =
    ((uniformLabelMeasure V A).map (orderedSetLabels S)).real E
  simp only [Measure.real, Measure.map_apply hmeas ((Set.toFinite E).measurableSet)]

end Erdos911
