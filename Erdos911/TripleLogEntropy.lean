import Erdos911.ConditionalSeedColoring
import Erdos911.ResidualParameterBounds

open Filter

namespace Erdos911

noncomputable def tripleLogEntropyThreshold (x : ℝ) : ℝ :=
  Real.log x - Real.log (Real.log (Real.log x)) - (Real.log 256 + 4)

theorem small_mark_rate_base_le_one (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1 / 2) :
    p * Real.exp (p / 4) ≤ 1 := by
  have hhalf := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
  norm_num at hhalf
  have hexp : Real.exp (p / 4) ≤ 2 := (Real.exp_le_exp.mpr (by linarith)).trans hhalf
  exact (mul_le_mul_of_nonneg_left hexp hp₀).trans (by linarith)

theorem residual_entropy_log_budget (x e entropy error L : ℝ)
    (hx : 0 < x) (hlog : 1 ≤ Real.log x) (hloglog : 1 ≤ Real.log (Real.log x))
    (he : 0 < e) (hp : baselineResidualRate x ≤ 1) (hL₀ : 0 ≤ L)
    (hL₁ : L ≤ e / Real.log x) (herror : error ≤ e)
    (hentropy : entropy ≤ e * tripleLogEntropyThreshold x) :
    entropy + error + (e - L) * (Real.log (baselineResidualRate x) + baselineResidualRate x / 4) < 0 := by
  have hLpos : 0 < Real.log x := by linarith
  have hUpos : 0 < Real.log (Real.log x) := by linarith
  have hp₀ : 0 < baselineResidualRate x := by unfold baselineResidualRate; positivity
  have hlogp : Real.log (baselineResidualRate x) =
      Real.log 256 + Real.log (Real.log (Real.log x)) - Real.log x := by
    unfold baselineResidualRate
    rw [Real.log_div (mul_pos (by norm_num) hUpos).ne' hx.ne', Real.log_mul (by norm_num) hUpos.ne']
  have hlogU : 0 ≤ Real.log (Real.log (Real.log x)) := Real.log_nonneg hloglog
  have hlog256 : 0 ≤ Real.log (256 : ℝ) := Real.log_nonneg (by norm_num)
  have hlower : -Real.log x ≤ Real.log (baselineResidualRate x) + baselineResidualRate x / 4 := by
    rw [hlogp]
    linarith
  have hupper : Real.log (baselineResidualRate x) + baselineResidualRate x / 4 ≤
      -Real.log x + Real.log (Real.log (Real.log x)) + Real.log 256 + 1 / 4 := by
    rw [hlogp]
    linarith
  have hallowance := (le_div_iff₀ hLpos).mp hL₁
  have hremoved := mul_le_mul_of_nonneg_left hlower hL₀
  have hremaining := mul_le_mul_of_nonneg_left hupper he.le
  unfold tripleLogEntropyThreshold at hentropy
  nlinarith only [hentropy, herror, hallowance, hremoved, hremaining, he]

theorem eventually_residual_entropy_parameters :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 1 ≤ d ∧ 1 ≤ Real.log d ∧ 1 ≤ Real.log (Real.log d) ∧
      0 < baselineResidualRate d ∧ baselineResidualRate d ≤ 1 / 2 ∧
      baselineResidualRate d * Real.exp (baselineResidualRate d / 4) ≤ 1 := by
  have hp := baselineResidualRate_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hl.and (hll.and hp))
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans
    (by exact_mod_cast (le_max_right 1 (Nat.ceil x₀)).trans hd)
  obtain ⟨hlog, hloglog, hrate⟩ := hx₀ d hx
  have hpos : 0 < baselineResidualRate d := by
    unfold baselineResidualRate
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  exact ⟨hd1, hlog, hloglog, hpos, hrate.le, small_mark_rate_base_le_one _ hpos.le hrate.le⟩

/-- The triple-log entropy threshold closes the conditional seed-coloring
criterion when earlier deletions cost at most `e/log(d)`. -/
theorem conditional_seed_triple_log_coloring {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : SimpleGraph U) [DecidableRel F.Adj]
    (K H J : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hHK : H ≤ K) (hJH : J ≤ H) (hFG : F.IsContained G) (hF : F.Connected)
    (d ΔG Δ D s q b : ℕ) (hd : 1 ≤ d)
    (hlogd : 1 ≤ Real.log d) (hloglog : 1 ≤ Real.log (Real.log d))
    (hΔG : ∀ v, G.degree v ≤ ΔG) (hhost : 0 < K.edgeFinset.card)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v)
    (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (τ : ℝ) (hτ : 0 < τ)
    (hp₀ : 0 < baselineResidualRate d) (hp₁ : baselineResidualRate d ≤ 1 / 2)
    (hlog : Real.log (8 * seedAssignmentCountBound (Fintype.card U) Δ D s q / baselineResidualRate d) ≤
      baselineResidualRate d * b / 2)
    (hcoverage : ∀ f : F.Copy H, ∃ a : SeedAssignment F H J s τ q,
      PartialAssignmentAgrees a.2.val f ∧ b ≤ (partialAssignmentEdges F J a.2.val).card)
    (L : ℝ) (hL₀ : 0 ≤ L) (hL₁ : L ≤ (G.edgeSet.ncard : ℝ) / Real.log d)
    (hdeleted : ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ L)
    (herror : forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent) K.edgeFinset.card ΔG ≤ G.edgeSet.ncard)
    (hentropy : componentEntropyMass G ≤ (G.edgeSet.ncard : ℝ) * tripleLogEntropyThreshold d) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  have he : (0 : ℝ) < G.edgeSet.ncard := by
    obtain ⟨u, v, huv⟩ := hedge
    exact_mod_cast (Set.ncard_pos (s := G.edgeSet)).mpr ⟨s(u, v), huv⟩
  apply conditional_seed_entropy_coloring G F K H J hHK hJH hFG hF ΔG Δ D hΔG hhost
    hneighbors hedge hΔ hD hΔpos hDpos s q b τ (baselineResidualRate d)
    hτ hp₀ (by linarith) hlog hcoverage L hdeleted (small_mark_rate_base_le_one _ hp₀.le hp₁)
  exact residual_entropy_log_budget d G.edgeSet.ncard (componentEntropyMass G)
    (forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent) K.edgeFinset.card ΔG) L
    (by exact_mod_cast (show 0 < d by omega)) hlogd hloglog he (by linarith) hL₀ hL₁ herror hentropy

end Erdos911
