import Erdos911.BlockMarkedEdges
import Erdos911.BiasedRedConditions

namespace Erdos911

/-- A block's extra edge multiplicity fits inside the exponential margin
in the anchored local-lemma estimate. -/
theorem block_red_weight_bounds (k b d D M : ℕ) (p : ℝ)
    (hk : 0 < k) (hd : 0 < d) (hdk : d ≤ k) (hD : 2 ≤ D)
    (haverage : d * k ≤ 2 * b) (hM : M ≤ D ^ k) (hp : 0 ≤ p)
    (hscale : 32 * Real.log D ≤ p * d) :
    Real.exp (-p * b / 2) ≤ 1 / 2 ∧
      (M * (k * D ^ (2 * (k - 1))) : ℝ) * Real.exp (-p * b / 2) ≤ 1 / d := by
  have hscalehalf : 16 * Real.log D ≤ (p / 2) * d := by nlinarith
  have hbase := anchored_red_weight_bounds k b d D (p / 2)
    hk hd hdk hD haverage (by positivity) hscalehalf
  have hexponent : -(p / 2) * (b : ℝ) / 2 = -p * b / 4 := by ring
  rw [hexponent] at hbase
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have havg : (d : ℝ) * k ≤ 2 * b := by exact_mod_cast haverage
  have hscale' := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg k)
  have havg' := mul_le_mul_of_nonneg_left havg hp
  have hmargin : (k : ℝ) * Real.log D ≤ p * b / 4 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hlog]
  have hMexp : (M : ℝ) ≤ Real.exp (p * b / 4) := by
    calc
      (M : ℝ) ≤ (D : ℝ) ^ k := by exact_mod_cast hM
      _ = Real.exp ((k : ℝ) * Real.log D) := by rw [Real.exp_nat_mul, Real.exp_log hDpos]
      _ ≤ Real.exp (p * b / 4) := Real.exp_le_exp.mpr hmargin
  have hMweight : (M : ℝ) * Real.exp (-p * b / 4) ≤ 1 := by
    calc
      _ ≤ Real.exp (p * b / 4) * Real.exp (-p * b / 4) :=
        mul_le_mul_of_nonneg_right hMexp (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add, show p * (b : ℝ) / 4 + -p * b / 4 = 0 by ring, Real.exp_zero]
  refine ⟨?_, ?_⟩
  · exact (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hp (Nat.cast_nonneg (α := ℝ) b)])).trans
      hbase.1
  · calc
      _ = ((k * D ^ (2 * (k - 1)) : ℝ) * Real.exp (-p * b / 4)) *
          ((M : ℝ) * Real.exp (-p * b / 4)) := by
        rw [show -p * (b : ℝ) / 2 = -p * b / 4 + -p * b / 4 by ring, Real.exp_add]
        ring
      _ ≤ (1 / d) * 1 := mul_le_mul hbase.2 hMweight
        (mul_nonneg (Nat.cast_nonneg M) (Real.exp_pos _).le) (by positivity)
      _ = 1 / d := mul_one _

theorem inverse_degree_block_parameters (d D : ℕ) (p : ℝ)
    (hd : 4 ≤ d) (hD : 2 ≤ D) (hscale : 32 * Real.log D ≤ p * d) :
    4 * (1 / (d : ℝ)) ≤ p ∧ Real.exp (2 * (1 / (d : ℝ))) ≤ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdreal : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hloghalf : 1 / 2 ≤ Real.log (2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogD : 1 / 2 ≤ Real.log D := hloghalf.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hD))
  have hq : 4 * (1 / (d : ℝ)) ≤ p := by
    rw [mul_one_div, div_le_iff₀ hdpos]
    nlinarith
  refine ⟨hq, ?_⟩
  have hqhalf : 2 * (1 / (d : ℝ)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ hdpos]
    linarith
  calc
    Real.exp (2 * (1 / (d : ℝ))) ≤ Real.exp (Real.log 2) :=
      Real.exp_le_exp.mpr (hqhalf.trans hloghalf)
    _ = 2 := Real.exp_log (by norm_num)

/-- Explicit degree-scale assumptions produce the block-rich deletion
with its target-capacity budget. -/
theorem exists_block_pruned_graph_of_degree_scale
    {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U)
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (P : Finset (RectangleBlock W)) (M b d D : ℕ) (hP : BoundedEdgeBlocks P M)
    (hd : 4 ≤ d) (hdk : d ≤ Fintype.card V) (hD : 2 ≤ D)
    (haverage : d * Fintype.card V ≤ 2 * b) (hM : M ≤ D ^ Fintype.card V)
    (hhost : ∀ w, H.degree w ≤ D) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hscale : 32 * Real.log D ≤ p * d)
    (c : P → ℝ) (hc : ∀ B, 0 ≤ c B)
    (hcapacity : ∀ g : G.Copy H, ∀ B, ((copyRawEdges g ∩ B.val.edges).card : ℝ) ≤ c B) :
    ∃ marked : Finset (Sym2 W),
      (∀ g : G.Copy H, ((copyRawEdges g ∩ marked).card : ℝ) ≤ (2 * p) * ∑ B, c B) ∧
      ∀ f : F.Copy (H.deleteEdges (marked : Set (Sym2 W))),
        (touchedBlocks P (copyRawEdges
          ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))).card < b := by
  have hdpos : 0 < d := by omega
  have hweights := block_red_weight_bounds (Fintype.card V) b d D M p
    (hdpos.trans_le hdk) hdpos hdk hD haverage hM hp₀ hscale
  have hparameters := inverse_degree_block_parameters d D p hd hD hscale
  exact exists_block_pruned_graph F G H hF P M hP b D hhost p (1 / d)
    hp₀ hp₁ hparameters.1 hweights.1 hweights.2 hparameters.2 c hc hcapacity

end Erdos911
