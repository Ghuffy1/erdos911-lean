import Mathlib.Data.Finset.Powerset
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

open MeasureTheory

namespace Erdos911

theorem fixed_subset_containing_card {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (x : V) (hx : x ∈ N) (hq : 0 < q) :
    ((N.powersetCard q).filter (fun S => x ∈ S)).card =
      (N.card - 1).choose (q - 1) := by
  have h := Finset.card_filter_powersetCard_subset {x} N q
    (Finset.singleton_subset_iff.mpr hx) (by simp only [Finset.card_singleton]; omega)
  simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using h

theorem fixed_subset_inclusion_ratio {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (x : V) (hx : x ∈ N) (hq : q ≤ N.card) :
    (((N.powersetCard q).filter (fun S => x ∈ S)).card : ℝ) /
        (N.powersetCard q).card = (q : ℝ) / N.card := by
  by_cases hqzero : q = 0
  · subst q
    simp
  have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
  have hNpos : 0 < N.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hchoose : 0 < N.card.choose q := Nat.choose_pos hq
  have hid : N.card * (N.card - 1).choose (q - 1) = N.card.choose q * q := by
    simpa only [Nat.sub_add_cancel hNpos, Nat.sub_add_cancel hqpos] using
      Nat.add_one_mul_choose_eq (N.card - 1) (q - 1)
  rw [fixed_subset_containing_card N q x hx hqpos, Finset.card_powersetCard]
  apply (div_eq_div_iff (by exact_mod_cast hchoose.ne') (by exact_mod_cast hNpos.ne')).mpr
  exact_mod_cast (by simpa only [Nat.mul_comm] using hid)

abbrev FixedSizeSubset {V : Type*} [DecidableEq V] (N : Finset V) (q : ℕ) :=
  {S : Finset V // S ∈ N.powersetCard q}

instance fixedSizeSubset_fintype {V : Type*} [DecidableEq V] (N : Finset V) (q : ℕ) :
    Fintype (FixedSizeSubset N q) := by
  unfold FixedSizeSubset
  infer_instance

instance fixedSizeSubset_measurableSpace {V : Type*} [DecidableEq V] (N : Finset V) (q : ℕ) :
    MeasurableSpace (FixedSizeSubset N q) := ⊤

instance fixedSizeSubset_measurableSingletonClass {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) : MeasurableSingletonClass (FixedSizeSubset N q) := by
  constructor
  intro S
  trivial

theorem fixedSizeSubset_nonempty {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (hq : q ≤ N.card) : Nonempty (FixedSizeSubset N q) := by
  obtain ⟨S, hSN, hS⟩ := Finset.exists_subset_card_eq hq
  exact ⟨⟨S, Finset.mem_powersetCard.mpr ⟨hSN, hS⟩⟩⟩

theorem fixedSizeSubset_card {V : Type*} [DecidableEq V] (N : Finset V) (q : ℕ) :
    Fintype.card (FixedSizeSubset N q) = N.card.choose q := by
  simp [FixedSizeSubset, Finset.card_powersetCard]

theorem fixedSizeSubset_event_card {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (x : V) :
    Fintype.card {S : FixedSizeSubset N q // x ∈ S.val} =
      ((N.powersetCard q).filter (fun S => x ∈ S)).card := by
  let e : {S : FixedSizeSubset N q // x ∈ S.val} ≃
      ↥((N.powersetCard q).filter (fun S => x ∈ S)) := {
    toFun := fun S => ⟨S.val.val, Finset.mem_filter.mpr ⟨S.val.property, S.property⟩⟩
    invFun := fun S => ⟨⟨S.val, (Finset.mem_filter.mp S.property).1⟩,
      (Finset.mem_filter.mp S.property).2⟩
    left_inv := by intro S; rfl
    right_inv := by intro S; rfl }
  simpa using Fintype.card_congr e

noncomputable def uniformSubsetMeasure {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (hq : q ≤ N.card) : Measure (FixedSizeSubset N q) := by
  letI := fixedSizeSubset_nonempty N q hq
  exact (PMF.uniformOfFintype (FixedSizeSubset N q)).toMeasure

instance uniformSubsetMeasure_isProbabilityMeasure {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (hq : q ≤ N.card) :
    IsProbabilityMeasure (uniformSubsetMeasure N q hq) := by
  unfold uniformSubsetMeasure
  infer_instance

/-- A fixed vertex belongs to a uniformly sampled q-element subset with
probability q divided by the neighborhood size. -/
theorem uniformSubsetMeasure_inclusion {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (hq : q ≤ N.card) (x : V) (hx : x ∈ N) :
    (uniformSubsetMeasure N q hq).real {S | x ∈ S.val} = (q : ℝ) / N.card := by
  classical
  let : Nonempty (FixedSizeSubset N q) := fixedSizeSubset_nonempty N q hq
  have hmeas : MeasurableSet {S : FixedSizeSubset N q | x ∈ S.val} :=
    (Set.toFinite _).measurableSet
  change ((PMF.uniformOfFintype (FixedSizeSubset N q)).toMeasure).real
    {S | x ∈ S.val} = (q : ℝ) / N.card
  have hmeasure := PMF.toMeasure_uniformOfFintype_apply
    (α := FixedSizeSubset N q) {S : FixedSizeSubset N q | x ∈ S.val} hmeas
  rw [Measure.real, hmeasure, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, fixedSizeSubset_card]
  change (Fintype.card {S : FixedSizeSubset N q // x ∈ S.val} : ℝ) /
    (N.card.choose q : ℝ) = _
  rw [fixedSizeSubset_event_card]
  simpa only [Finset.card_powersetCard] using fixed_subset_inclusion_ratio N q x hx hq

theorem uniformSubsetMeasure_outside {V : Type*} [DecidableEq V]
    (N : Finset V) (q : ℕ) (hq : q ≤ N.card) (x : V) (hx : x ∉ N) :
    (uniformSubsetMeasure N q hq).real {S | x ∈ S.val} = 0 := by
  have hempty : {S : FixedSizeSubset N q | x ∈ S.val} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hx ((Finset.mem_powersetCard.mp S.property).1 h)
  rw [hempty]
  exact measureReal_empty

end Erdos911
