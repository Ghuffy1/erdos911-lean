import Erdos911.UniformLabelRestriction
import Erdos911.DisjointEventTails

open MeasureTheory

namespace Erdos911

def labelSubsetEvent {V A : Type*} (v : V) (S : Finset A) : Set (V → A) :=
  {f | f v ∈ S}

theorem labelSubsetEvent_depends {V A : Type*} (v : V) (S : Finset A) :
    DependsOnlyOn (labelSubsetEvent v S) {v} := by
  intro f g heq hf
  change g v ∈ S
  rw [← heq v (Finset.mem_singleton_self _)]
  exact hf

theorem labelSubsetEvent_probability {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [Nonempty A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (v : V) (S : Finset A) :
    (uniformLabelMeasure V A).real (labelSubsetEvent v S) ≤ S.card / (Fintype.card A : ℝ) := by
  classical
  let E (a : ↥S) : Set (V → A) := labelPattern {v} (fun _ => a.val)
  have hcover : labelSubsetEvent v S ⊆ ⋃ a, E a := by
    intro f hf
    refine Set.mem_iUnion.mpr ⟨⟨f v, hf⟩, ?_⟩
    intro w hw
    have heq : w = v := Finset.mem_singleton.mp hw
    subst w
    rfl
  have hp (a : ↥S) : (uniformLabelMeasure V A).real (E a) = 1 / (Fintype.card A : ℝ) := by
    rw [uniformLabelMeasure_pattern]
    simp only [Finset.card_singleton, pow_one]
  have hsum : (∑ a : ↥S, (uniformLabelMeasure V A).real (E a)) = S.card / (Fintype.card A : ℝ) := by
    simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    ring
  exact ((measureReal_mono hcover).trans (measureReal_iUnion_fintype_le E)).trans_eq hsum

/-- The number of independent row labels falling in a fixed coordinate
subset has the usual finite binomial upper bound. -/
theorem uniform_subset_hits_tail {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [Nonempty A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (U : Finset V) (S : Finset A) (t : ℕ) :
    (uniformLabelMeasure V A).real {f | t ≤ (eventHitSet (fun v => labelSubsetEvent v S) U f).card} ≤
      (U.card.choose t : ℝ) * (S.card / (Fintype.card A : ℝ)) ^ t := by
  have h := disjoint_coordinate_events_tail
    (fun _ : V => (PMF.uniformOfFintype A).toMeasure) (fun v => labelSubsetEvent v S)
    (fun v => {v}) (fun v => labelSubsetEvent_depends v S)
    (fun v w hvw => Finset.disjoint_singleton.mpr hvw) U t
    (S.card / (Fintype.card A : ℝ)) (by positivity)
    (fun v _ => labelSubsetEvent_probability v S)
  exact h

theorem uniform_subset_hits_tail_ratio {V A : Type*} [Fintype V] [DecidableEq V]
    [Fintype A] [Nonempty A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (U : Finset V) (S : Finset A) (t : ℕ) (r : ℝ) (ht : 0 < t) (hr : 0 ≤ r)
    (hsize : (U.card : ℝ) ≤ r * t) :
    (uniformLabelMeasure V A).real {f | t ≤ (eventHitSet (fun v => labelSubsetEvent v S) U f).card} ≤
      (Real.exp 1 * r * S.card / Fintype.card A) ^ t := by
  classical
  by_cases htU : t ≤ U.card
  · have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have hp : 0 ≤ (S.card : ℝ) / Fintype.card A := by positivity
    have hbase : Real.exp 1 * U.card * (S.card / (Fintype.card A : ℝ)) / t ≤
        Real.exp 1 * r * S.card / Fintype.card A := by
      apply (div_le_iff₀ htR).mpr
      have hm := mul_le_mul_of_nonneg_left hsize
        (show 0 ≤ Real.exp 1 * (S.card / (Fintype.card A : ℝ)) by positivity)
      convert hm using 1 <;> ring
    exact ((uniform_subset_hits_tail U S t).trans
      (choose_mul_pow_bound U.card t ht htU _ hp)).trans
      (pow_le_pow_left₀ (by positivity) hbase t)
  · have hset : {f : V → A | t ≤ (eventHitSet (fun v => labelSubsetEvent v S) U f).card} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro f hf
      have hsub : eventHitSet (fun v => labelSubsetEvent v S) U f ⊆ U := Finset.filter_subset _ _
      exact htU (hf.trans (Finset.card_le_card hsub))
    rw [hset, measureReal_empty]
    positivity

end Erdos911
