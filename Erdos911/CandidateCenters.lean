import Erdos911.MomentBound
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos911

noncomputable def commonCenters {X Z : Type*} [Fintype Z]
    (R : X → Z → Prop) (Y : Finset X) : Finset Z := by
  classical
  exact Finset.univ.filter fun z => ∀ x ∈ Y, R x z

noncomputable def candidatesAt {X Z : Type*}
    (R : X → Z → Prop) (Y : Finset X) (z : Z) : Finset X := by
  classical
  exact Y.filter fun x => R x z

/-- Double-count tuples of candidates together with a common center.
Allowing repeated candidates avoids any binomial-coefficient approximation. -/
theorem common_center_tuple_count {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X]
    (R : X → Z → Prop) (Y : Finset X) (s : ℕ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin s => Y),
        (commonCenters R (Finset.univ.image f)).card =
      ∑ z : Z, (candidatesAt R Y z).card ^ s := by
  classical
  have hcenters (f : Fin s → X) : commonCenters R (Finset.univ.image f) =
      Finset.univ.filter (fun z => ∀ i, R (f i) z) := by
    ext z
    simp [commonCenters]
  simp_rw [hcenters]
  conv_lhs => simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have htuples : (Fintype.piFinset (fun _ : Fin s => Y)).filter
      (fun f => ∀ i, R (f i) z) =
      Fintype.piFinset (fun _ : Fin s => candidatesAt R Y z) := by
    ext f
    simp only [Finset.mem_filter, Fintype.mem_piFinset, candidatesAt]
    exact forall_and.symm
  calc
    (∑ f ∈ Fintype.piFinset (fun _ : Fin s => Y), if ∀ i, R (f i) z then 1 else 0) =
        ((Fintype.piFinset (fun _ : Fin s => Y)).filter
          (fun f => ∀ i, R (f i) z)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = (candidatesAt R Y z).card ^ s := by
      rw [htuples, Fintype.card_piFinset_const]

theorem candidate_incidence_count {X Z : Type*} [Fintype Z]
    (R : X → Z → Prop) (Y : Finset X) :
    ∑ z : Z, (candidatesAt R Y z).card =
      ∑ x ∈ Y, (commonCenters R {x}).card := by
  classical
  simp only [candidatesAt, commonCenters, Finset.mem_singleton,
    forall_eq, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- The numerical decay estimate used with the center moments. -/
theorem center_log_decay (D T : ℝ) (r : ℕ)
    (hD : 0 < D) (hT : 0 < T) (hr : 0 < r)
    (hθ : Real.log (2 * D / T) / r < 1) :
    D * (1 - Real.log (2 * D / T) / r) ^ r ≤ T / 2 := by
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  let θ := Real.log (2 * D / T) / r
  have hbase : 0 ≤ 1 - θ := by dsimp [θ]; linarith
  have hexp : 1 - θ ≤ Real.exp (-θ) := by
    have h := Real.add_one_le_exp (-θ)
    linarith
  have hpow := pow_le_pow_left₀ hbase hexp r
  have hexact : (Real.exp (-θ)) ^ r = T / (2 * D) := by
    rw [← Real.exp_nat_mul]
    have heq : (r : ℝ) * -θ = -Real.log (2 * D / T) := by
      dsimp [θ]
      field_simp
    rw [heq, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [hexact] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow hD.le
  have hcancel : D * (T / (2 * D)) = T / 2 := by field_simp
  simpa only [hcancel] using hmul

/-- The two normalized moment bounds obtained from common neighborhoods. -/
theorem candidate_moments {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X]
    (R : X → Z → Prop) (Y : Finset X) (s : ℕ) (D T : ℝ)
    (hY : Y.Nonempty)
    (hD : ∀ x ∈ Y, ((commonCenters R {x}).card : ℝ) ≤ D)
    (hcommon : ∀ W ⊆ Y, W.card ≤ s → T ≤ ((commonCenters R W).card : ℝ)) :
    (∑ z : Z, ((candidatesAt R Y z).card : ℝ) / Y.card) ≤ D ∧
      T ≤ ∑ z : Z, (((candidatesAt R Y z).card : ℝ) / Y.card) ^ s := by
  classical
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hinc : (∑ z : Z, ((candidatesAt R Y z).card : ℝ)) =
      ∑ x ∈ Y, ((commonCenters R {x}).card : ℝ) := by
    exact_mod_cast candidate_incidence_count R Y
  have hfirst : (∑ z : Z, ((candidatesAt R Y z).card : ℝ)) ≤ (Y.card : ℝ) * D := by
    rw [hinc]
    calc
      (∑ x ∈ Y, ((commonCenters R {x}).card : ℝ)) ≤ ∑ x ∈ Y, D :=
        Finset.sum_le_sum hD
      _ = (Y.card : ℝ) * D := by simp
  let tuples := Fintype.piFinset (fun _ : Fin s => Y)
  have htuple : ∀ f ∈ tuples,
      T ≤ ((commonCenters R (Finset.univ.image f)).card : ℝ) := by
    intro f hf
    apply hcommon
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact Fintype.mem_piFinset.mp hf i
    · exact (Finset.card_image_le).trans (by simp)
  have hsecond : T * (Y.card : ℝ) ^ s ≤
      ∑ z : Z, ((candidatesAt R Y z).card : ℝ) ^ s := by
    calc
      T * (Y.card : ℝ) ^ s = ∑ f ∈ tuples, T := by
        simp [tuples, mul_comm]
      _ ≤ ∑ f ∈ tuples, ((commonCenters R (Finset.univ.image f)).card : ℝ) :=
        Finset.sum_le_sum htuple
      _ = ∑ z : Z, ((candidatesAt R Y z).card : ℝ) ^ s := by
        exact_mod_cast common_center_tuple_count R Y s
  constructor
  · rw [← Finset.sum_div]
    apply (div_le_iff₀ hYpos).mpr
    simpa [mul_comm] using hfirst
  · calc
      T ≤ (∑ z : Z, ((candidatesAt R Y z).card : ℝ) ^ s) / (Y.card : ℝ) ^ s :=
        (le_div_iff₀ (pow_pos hYpos s)).mpr hsecond
      _ = ∑ z : Z, (((candidatesAt R Y z).card : ℝ) / Y.card) ^ s := by
        simp_rw [div_pow]
        rw [Finset.sum_div]

/-- Corrected candidate-list center lemma. Every parameter restriction needed
by the logarithmic formula is explicit, including `2 ≤ s`. -/
theorem candidate_list_centers {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X]
    (R : X → Z → Prop) (Y : Finset X) (s : ℕ) (D T : ℝ)
    (hs : 2 ≤ s) (hY : Y.Nonempty) (hDpos : 0 < D) (hTpos : 0 < T)
    (hD : ∀ x ∈ Y, ((commonCenters R {x}).card : ℝ) ≤ D)
    (hcommon : ∀ W ⊆ Y, W.card ≤ s → T ≤ ((commonCenters R W).card : ℝ))
    (hθ : Real.log (2 * D / T) / ((s - 1 : ℕ) : ℝ) < 1) :
    T / 2 ≤ (Finset.univ.filter fun z : Z =>
      1 - Real.log (2 * D / T) / ((s - 1 : ℕ) : ℝ) ≤
        ((candidatesAt R Y z).card : ℝ) / Y.card).card := by
  classical
  let f : Z → ℝ := fun z => ((candidatesAt R Y z).card : ℝ) / Y.card
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hf₀ : ∀ z ∈ (Finset.univ : Finset Z), 0 ≤ f z := by
    intro z _
    exact div_nonneg (Nat.cast_nonneg _) hYpos.le
  have hf₁ : ∀ z ∈ (Finset.univ : Finset Z), f z ≤ 1 := by
    intro z _
    apply (div_le_one hYpos).mpr
    exact_mod_cast Finset.card_filter_le Y (fun x => R x z)
  have hmoment := candidate_moments R Y s D T hY hD hcommon
  have hs1 : 1 ≤ s := by omega
  have hpower : T ≤ ∑ z : Z, f z ^ (s - 1 + 1) := by
    simpa only [Nat.sub_add_cancel hs1] using hmoment.2
  have hdecay := center_log_decay D T (s - 1) hDpos hTpos (by omega) hθ
  exact centers_from_moments Finset.univ f (s - 1)
    (1 - Real.log (2 * D / T) / ((s - 1 : ℕ) : ℝ)) D T
    (by linarith) hf₀ hf₁ hmoment.1 hpower hdecay

end Erdos911
