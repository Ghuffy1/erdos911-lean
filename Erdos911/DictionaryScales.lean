import Erdos911.DyadicScaleCount
import Erdos911.ConcreteDictionaryLabels

namespace Erdos911

def AdmissibleDictionaryScale {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V) (j : ℕ) : Prop :=
  8 * dictionaryLeftSize q * dictionaryLowDegree q ≤ q * 2 ^ j ∧
    (∀ x ∈ W, 2 ^ j ≤ 8 * dictionaryPatternCount q * K.degree x) ∧
    (∀ x ∈ W, K.degree x < 2 * dictionaryDegreeCharge q * 2 ^ j)

noncomputable def dictionaryScales {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V) : Finset ℕ := by
  classical
  exact (Finset.range (8 * dictionaryPatternCount q * K.maxDegree + 1)).filter
    (AdmissibleDictionaryScale K q W)

theorem mem_dictionaryScales {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V)
    (hW : W.Nonempty) (j : ℕ) :
    j ∈ dictionaryScales K q W ↔ AdmissibleDictionaryScale K q W j := by
  classical
  constructor
  · intro hj
    exact (Finset.mem_filter.mp hj).2
  · intro hj
    obtain ⟨x, hx⟩ := hW
    have hp : j ≤ 2 ^ j := Nat.le_of_lt j.lt_two_pow_self
    have hbound := (hj.2.1 x hx).trans (Nat.mul_le_mul_left _ (K.degree_le_maxDegree x))
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj⟩

/-- The number of admissible dyadic scales is bounded independently
of the largest host degree. A coarse multiplicative-range bound suffices. -/
theorem dictionaryScales_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V) (hW : W.Nonempty) :
    (dictionaryScales K q W).card ≤ 16 * dictionaryPatternCount q * dictionaryDegreeCharge q := by
  classical
  have hM : 0 < dictionaryPatternCount q := by
    unfold dictionaryPatternCount
    positivity
  obtain ⟨x, hx⟩ := hW
  apply dyadic_scale_card_bound
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  calc
    2 ^ j ≤ 8 * dictionaryPatternCount q * K.degree x := hj'.2.1 x hx
    _ < 8 * dictionaryPatternCount q * (2 * dictionaryDegreeCharge q * 2 ^ k) :=
      Nat.mul_lt_mul_of_pos_left (hk'.2.2 x hx) (by positivity)
    _ = (16 * dictionaryPatternCount q * dictionaryDegreeCharge q) * 2 ^ k := by ring

end Erdos911
