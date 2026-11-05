import Erdos911.CollisionProbability
import Erdos911.ConnectedLabelWeights

open MeasureTheory

namespace Erdos911

theorem collision_label_weight_bounds (D u : ℕ) (hD : 2 ≤ D) (hu : 0 < u) :
    0 ≤ (1 / ((D : ℝ) + 1)) ^ (4 * u) ∧
    (1 / ((D : ℝ) + 1)) ^ (4 * u) ≤ 1 / 2 ∧
    (1 / ((D : ℝ) + 1)) ^ (10 * u) ≤
      (1 / ((D : ℝ) + 1)) ^ (4 * u) * Real.exp (-2 * ((1 / 8 : ℝ) * u)) := by
  let t : ℝ := 1 / ((D : ℝ) + 1)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htthird : t ≤ 1 / 3 := by
    apply one_div_le_one_div_of_le (by norm_num)
    exact_mod_cast (show 3 ≤ D + 1 by omega)
  have ht1 : t ≤ 1 := htthird.trans (by norm_num)
  have hsmall : t ^ (4 * u) ≤ t := by
    simpa only [pow_one] using pow_le_pow_of_le_one ht0 ht1 (show 1 ≤ 4 * u by omega)
  have hsix : t ^ 6 ≤ Real.exp (-(1 / 4 : ℝ)) := by
    have hpower : t ^ 6 ≤ t := by
      simpa only [pow_one] using pow_le_pow_of_le_one ht0 ht1 (show 1 ≤ 6 by norm_num)
    have he := Real.add_one_le_exp (-(1 / 4 : ℝ))
    linarith
  have hpow := pow_le_pow_left₀ (pow_nonneg ht0 6) hsix u
  have heq : Real.exp (-(1 / 4 : ℝ)) ^ u = Real.exp (-2 * ((1 / 8 : ℝ) * u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine ⟨pow_nonneg ht0 _, hsmall.trans (htthird.trans (by norm_num)), ?_⟩
  change t ^ (10 * u) ≤ t ^ (4 * u) * _
  calc
    t ^ (10 * u) = t ^ (4 * u) * (t ^ 6) ^ u := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ t ^ (4 * u) * Real.exp (-(1 / 4 : ℝ)) ^ u :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg ht0 _)
    _ = _ := by rw [heq]

/-- A single labeling has few repeated labels in every small connected
vertex set. The size of the ambient graph does not enter the palette bound. -/
theorem exists_sparse_collision_labeling {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D K k : ℕ)
    (hD : 2 ≤ D) (hk : 2 ≤ k) (hmax : ∀ v, G.degree v ≤ D)
    (hpalette : K * (D + 1) ^ (12 * k) ≤ Fintype.card A) :
    ∃ f : V → A, ∀ S : Finset V, S.card ≤ K → (G.induce (S : Set V)).Connected →
      k * (repeatedVertices S f).card ≤ 2 * S.card := by
  classical
  let : MeasurableSpace A := ⊤
  let : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  let F := smallConnectedSets G K
  let events (S : ↥F) := excessiveCollisions (A := A) S.val k
  let weights (S : ↥F) : ℝ := (1 / ((D : ℝ) + 1)) ^ (4 * S.val.card)
  have hinfo (S : ↥F) := (mem_smallConnectedSets G K S.val).mp S.property
  have hbudget (v : V) :
      (∑ S ∈ (Finset.univ : Finset ↥F).filter (fun S => v ∈ S.val), weights S) ≤ 1 / 8 := by
    rw [Finset.sum_filter]
    change (∑ S : ↥F, if v ∈ S.val then
      (1 / ((D : ℝ) + 1)) ^ (4 * S.val.card) else 0) ≤ _
    rw [Finset.sum_coe_sort F (fun S => if v ∈ S then
      (1 / ((D : ℝ) + 1)) ^ (4 * S.card) else 0), ← Finset.sum_filter]
    exact connected_label_coordinate_budget G D K hD hmax v
  have hweight0 (S : ↥F) : 0 ≤ weights S := (collision_label_weight_bounds D S.val.card hD (hinfo S).1).1
  have hweightHalf (S : ↥F) : weights S ≤ 1 / 2 :=
    (collision_label_weight_bounds D S.val.card hD (hinfo S).1).2.1
  have hprob (S : ↥F) : (uniformLabelMeasure V A).real (events S) ≤
      weights S * Real.exp (-2 * ((1 / 8 : ℝ) * S.val.card)) :=
    (excessiveCollisions_probability S.val K D k (hinfo S).1 (hinfo S).2.1 hD hk hpalette).trans
      (collision_label_weight_bounds D S.val.card hD (hinfo S).1).2.2
  have hLLL := coordinate_lll_from_exp_bounds_fintype
    (fun _ : V => (PMF.uniformOfFintype A).toMeasure) events (fun S => S.val)
    (fun S => excessiveCollisions_depends S.val k) weights (1 / 8)
    hweight0 hweightHalf hbudget hprob
  have hnonempty : (avoidAll events).Nonempty := by
    by_contra hn
    have hz : avoidAll events = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hp := hLLL.1
    rw [hz, measureReal_empty] at hp
    exact lt_irrefl 0 hp
  obtain ⟨f, hf⟩ := hnonempty
  refine ⟨f, ?_⟩
  intro S hSK hconn
  have hpos : 0 < S.card := by
    obtain ⟨v⟩ := hconn.nonempty
    exact Finset.card_pos.mpr ⟨v.val, v.property⟩
  have hSF : S ∈ F := (mem_smallConnectedSets G K S).mpr ⟨hpos, hSK, hconn⟩
  have hcollision : k * (collisionIndices (orderedSetLabels S f)).card ≤ S.card :=
    Nat.le_of_not_gt (hf ⟨S, hSF⟩)
  calc
    k * (repeatedVertices S f).card ≤ k * (2 * (collisionIndices (orderedSetLabels S f)).card) :=
      Nat.mul_le_mul_left k (repeatedVertices_card_le_twice_collisions S f)
    _ = 2 * (k * (collisionIndices (orderedSetLabels S f)).card) := by ring
    _ ≤ 2 * S.card := Nat.mul_le_mul_left 2 hcollision

end Erdos911
