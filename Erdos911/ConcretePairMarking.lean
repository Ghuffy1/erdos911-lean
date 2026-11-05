import Erdos911.PairMarkingParameters
import Erdos911.PairMarkingSelection

namespace Erdos911

/-- A dense connected pair pattern can be blocked while only a
d^(-8) fraction of the host rows acquire large blue degree. All local
lemma parameters are discharged, independently of the left degree scale. -/
theorem exists_concrete_pair_marking {V L R : Type*}
    [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] [Fintype R]
    (F : SimpleGraph V) [DecidableRel F.Adj] (U : SimpleGraph L) [DecidableRel U.Adj]
    (hF : F.Connected) (D d : ℕ) (hD : 2 ≤ D) (hd : 65536 ≤ d)
    (hU : ∀ x, U.degree x ≤ D) (horder : d ≤ Fintype.card V)
    (hdense : 32 * (Fintype.card V : ℝ) * Real.log D ≤
      lightPairProbability d * F.edgeSet.ncard)
    (N : R → Finset L) (hrows : ∀ y, (N y).card ^ 2 ≤ 1024 * d ^ 5) :
    ∃ ω : Sym2 L → Bool,
      (∀ f : F.Copy U, ω ∉ fixedBits (copyRawEdges f) false) ∧
      ((pairBadRows N d ω).card : ℝ) ≤ (2 / (d : ℝ) ^ 8) * Fintype.card R := by
  classical
  obtain ⟨hρ0, hρ1, hη0, hsmall, hηhalf⟩ := light_pair_basic_parameters d hd
  have hweight := pair_pattern_weight_bound D (Fintype.card V) d F.edgeSet.ncard (lightPairProbability d)
    hD (by omega) horder hdense
  have hhalf := (pair_pattern_single_weight_bound D (Fintype.card V) d F.edgeSet.ncard
    (lightPairProbability d) hD (by omega) horder hdense).trans hηhalf
  have hsize (y : R) : (N y).sym2.card ≤ lightPairTailFactor d * (d / 4) :=
    light_pair_row_size_bound d _ hd ((row_pair_count_le_square (N y)).trans (hrows y))
  have hcorrection (y : R) : Real.exp (2 * (lightPairWeightBudget d * (N y).sym2.card)) ≤ 2 := by
    apply light_pair_correction_bound d hd
    exact_mod_cast (row_pair_count_le_square (N y)).trans (hrows y)
  obtain ⟨ω, havoid, hbad⟩ := exists_pair_marking_with_few_bad_rows F U hF D hU N d (lightPairTailFactor d)
    (by omega) hsize (lightPairProbability d) (lightPairWeightBudget d) hρ0 hρ1 hη0 hsmall hhalf
    hweight hcorrection
  refine ⟨ω, havoid, hbad.trans ?_⟩
  have htail := light_pair_tail_bound d hd
  have hm := mul_le_mul_of_nonneg_right htail (show 0 ≤ 2 * (Fintype.card R : ℝ) by positivity)
  convert hm using 1 <;> ring

end Erdos911
