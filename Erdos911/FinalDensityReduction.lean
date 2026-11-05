import Erdos911.HighBandReduction
import Erdos911.ProofInterface

namespace Erdos911

/-- A uniform minimum-degree theorem implies the exact average-density
statement, with all isolated vertices, strictness, and quantifiers retained. -/
theorem exact_of_minimum_degree_statement (h : MinimumDegreeRamseyStatement) : ExactStatement := by
  apply exact_iff_fixedMultipliers.mpr
  intro k
  let M : ℝ := 8 * ((k : ℝ) + 1)
  have hM : 1 ≤ M := by dsimp only [M]; nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨d₀, hd₀⟩ := h M hM
  refine ⟨max 4 (4 * (d₀ : ℝ)), ?_⟩
  intro C hC n G hn hCG
  classical
  have hC4 : 4 ≤ C := (le_max_left _ _).trans hC
  have hCpos : 0 < C := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heG : (0 : ℝ) < G.edgeSet.ncard := (mul_pos hCpos hnR).trans_le hCG
  let d := Nat.ceil (C / 4)
  have hdlo : C / 4 ≤ (d : ℝ) := Nat.le_ceil _
  have hdhi : (d : ℝ) ≤ C / 2 := by
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ C / 4 by positivity)).le
    change (d : ℝ) ≤ C / 4 + 1 at hceil
    linarith only [hceil, hC4]
  have hdd₀ : d₀ ≤ d := by
    have hd₀C : 4 * (d₀ : ℝ) ≤ C := (le_max_right _ _).trans hC
    have hd₀d : (d₀ : ℝ) ≤ d := by linarith only [hd₀C, hdlo]
    exact_mod_cast hd₀d
  obtain ⟨S, F, hFG, hFmin, hFmass⟩ := exists_density_core G C hCpos.le
    (by simpa only [G.edgeFinset_card, Set.fintypeCard_eq_ncard, Fintype.card_fin] using hCG)
  let : DecidableRel F.Adj := Classical.decRel _
  rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hFmass
  have hFe : 0 < F.edgeSet.ncard := by
    have hr : (0 : ℝ) < F.edgeSet.ncard := lt_of_lt_of_le (by positivity) hFmass
    exact_mod_cast hr
  have hcard : 0 < Fintype.card S := by
    obtain ⟨e, he⟩ := (Set.ncard_pos (s := F.edgeSet)).mp hFe
    induction e using Sym2.inductionOn with
    | _ u v => exact Fintype.card_pos_iff.mpr ⟨u⟩
  have hFd : ∀ v, d ≤ F.degree v := by
    intro v
    have hr : (d : ℝ) ≤ (F.neighborSet v).ncard := hdhi.trans (hFmin v)
    rw [F.ncard_neighborSet] at hr
    exact_mod_cast hr
  have hbound := hd₀ d hdd₀ S F hcard hFd
  have hmono : (SimpleGraph.sizeRamsey F F : ℝ) ≤ SimpleGraph.sizeRamsey G G := by
    exact_mod_cast sizeRamsey_mono hFG hFG
  have hcoef : (k : ℝ) * C ≤ M * d / 2 := by
    have hm := mul_le_mul_of_nonneg_left hdlo (show 0 ≤ 4 * ((k : ℝ) + 1) by positivity)
    dsimp only [M]
    nlinarith only [hm, hCpos]
  have heG0 : (0 : ℝ) ≤ G.edgeSet.ncard := heG.le
  have hbudget : (k : ℝ) * C * G.edgeSet.ncard ≤ (M * d) * F.edgeSet.ncard := by
    have h₁ := mul_le_mul_of_nonneg_right hcoef heG0
    have h₂ := mul_le_mul_of_nonneg_left hFmass (show 0 ≤ M * (d : ℝ) by positivity)
    nlinarith only [h₁, h₂]
  exact hbudget.trans_lt (hbound.trans_le hmono)

/-- Completing any one high-band exponent A>=1 would close the exact
upstream theorem. The high-band premise has not yet been proved. -/
theorem exact_of_high_degree_bands (A : ℕ) (hA : 1 ≤ A) (hHigh : HighDegreeBandStatement A) :
    ExactStatement :=
  exact_of_minimum_degree_statement (minimum_degree_statement_of_high_bands A hA hHigh)

end Erdos911
