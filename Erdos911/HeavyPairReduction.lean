import Erdos911.LightPairRamsey
import Erdos911.StrongUnbalancedReduction

namespace Erdos911

/-- The heavy-pair statement used by the reduction. At least half the right
rows concentrate in a closed heavy-pair ball. The degree scale P and
the number and diversity of the resulting blocks remain unrestricted. -/
def HeavyPairRamseyStatement : Prop :=
  ∀ M : ℝ, 1 ≤ M → ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (L R : Type) [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
      (S : R → Finset L) (P : ℝ),
      0 < Fintype.card L → (d : ℝ) ^ 200 ≤ P →
      (∀ y, (S y).card = d) →
      (∀ x, P ≤ (incidenceColumn S x).card) →
      (∀ x, ((incidenceColumn S x).card : ℝ) ≤ (d : ℝ) ^ 4 * P) →
      Fintype.card R < 2 * (heavyConcentratedRows S (P / (d : ℝ) ^ 12) (d / 4)).card →
      (M * d) * (incidenceGraph S).edgeSet.ncard <
        (SimpleGraph.sizeRamsey (incidenceGraph S) (incidenceGraph S) : ℝ)

/-- The light and heavy cases combine into the strongly unbalanced statement. -/
theorem strongly_unbalanced_of_heavy_pairs (h : HeavyPairRamseyStatement) :
    StronglyUnbalancedRamseyStatement := by
  intro M hM
  obtain ⟨d₀, hd₀⟩ := h M hM
  refine ⟨max d₀ (max 65536 (Nat.ceil (M ^ 2))), ?_⟩
  intro d hd L R _ _ _ _ S P hcard hP hright hleft hmax
  have hdd₀ : d₀ ≤ d := (le_max_left _ _).trans hd
  have hd65536 : 65536 ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hceil : Nat.ceil (M ^ 2) ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  have hM2 : M ^ 2 ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hrow (y : R) : (S y).card = d := by simpa only [incidenceGraph_degree_right] using hright y
  have hL : 0 < Fintype.card L := by
    by_contra hn
    have hL0 : Fintype.card L = 0 := by omega
    have hR : 0 < Fintype.card R := by simpa only [Fintype.card_sum, hL0, zero_add] using hcard
    obtain ⟨y⟩ := Fintype.card_pos_iff.mp hR
    have hs := Finset.card_le_univ (S y)
    rw [hrow y, hL0] at hs
    omega
  have hcol (x : L) : P ≤ (incidenceColumn S x).card := by
    simpa only [incidenceGraph_degree_left, incidenceColumn] using hleft x
  have hcap (x : L) : ((incidenceColumn S x).card : ℝ) ≤ (d : ℝ) ^ 4 * P := by
    simpa only [incidenceGraph_degree_left, incidenceColumn] using hmax x
  by_cases hfew : 2 * (heavyConcentratedRows S (P / (d : ℝ) ^ 12) (d / 4)).card ≤ Fintype.card R
  · exact light_pair_size_ramsey_lower_bound S d M P hd65536 hM hM2 hP hL hrow hcol hcap hfew
  · exact hd₀ d hdd₀ L R S P hL hP hrow hcol hcap (lt_of_not_ge hfew)

/-- The exact implication from the heavy-pair statement; its premise
is supplied by the large-right-block theorem in FullProof. -/
theorem exact_of_heavy_pairs (h : HeavyPairRamseyStatement) : ExactStatement :=
  exact_of_strongly_unbalanced (strongly_unbalanced_of_heavy_pairs h)

end Erdos911
