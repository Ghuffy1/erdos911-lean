import Erdos911.BlockBudgetBounds
import Erdos911.HostPruningComposition

open Filter

namespace Erdos911

noncomputable def baselineTargetDensity (B : ℕ) (x : ℝ) : ℝ :=
  4096 * ((B : ℝ) + 1) * baselineHostMultiplier x * Real.log x

noncomputable def baselineDegreeCutoff (B d : ℕ) : ℕ :=
  Nat.ceil (32 * baselineHostMultiplier d * (d ^ B : ℕ))

noncomputable def baselineDensityCutoff (B d : ℕ) : ℕ :=
  Nat.ceil (32 * baselineHostMultiplier d * baselineTargetDensity B d)

theorem baselineHostMultiplier_bounds (d : ℕ) (hd : 1 ≤ d)
    (hloglog : 1 ≤ Real.log (Real.log d)) (hp : baselineResidualRate d ≤ 1 / 64) :
    1 ≤ baselineHostMultiplier d ∧ baselineHostMultiplier d ≤ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hden : 0 < 16384 * Real.log (Real.log d) := by linarith
  have hprob : 256 * Real.log (Real.log d) ≤ (1 / 64 : ℝ) * d :=
    (div_le_iff₀ hdpos).mp hp
  constructor
  · unfold baselineHostMultiplier
    apply (one_le_div hden).mpr
    linarith
  · unfold baselineHostMultiplier
    apply (div_le_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left hloglog hdpos.le
    nlinarith

theorem eventually_baseline_host_parameters :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 131072 ≤ d ∧ 32768 ≤ Real.log d ∧
      1 ≤ Real.log (Real.log d) ∧ 1 ≤ baselineHostMultiplier d ∧ baselineHostMultiplier d ≤ d := by
  have hp := baselineResidualRate_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 64 by norm_num))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (32768 : ℝ))
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hl.and (hll.and hp))
  refine ⟨max 131072 (Nat.ceil x₀), ?_⟩
  intro d hd
  have hdlarge : 131072 ≤ d := (le_max_left _ _).trans hd
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans
    (by exact_mod_cast (le_max_right 131072 (Nat.ceil x₀)).trans hd)
  obtain ⟨hlog, hloglog, hprob⟩ := hx₀ d hx
  have hbounds := baselineHostMultiplier_bounds d (by omega) hloglog hprob.le
  exact ⟨hdlarge, hlog, hloglog, hbounds.1, hbounds.2⟩

theorem polynomialDensityCoefficient_bound (B d : ℕ) (Λ : ℝ) (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log d) (hΛ : 1 ≤ Λ) :
    2048 * Λ * Real.log ((d ^ B : ℕ) + 1) + 5 / 2 ≤ 4096 * ((B : ℝ) + 1) * Λ * Real.log d := by
  have hpower : 1 ≤ d ^ B := Nat.one_le_pow B d hd
  have hlogpower := log_polynomial_successor_le B d (d ^ B) hpower le_rfl
  have hΛpos : 0 ≤ Λ := by linarith
  have hlogpos : 0 ≤ Real.log d := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hlogpower
    (show 0 ≤ 2048 * Λ by positivity)
  have hlogscaled := mul_le_mul_of_nonneg_left hlog hΛpos
  have hB := mul_nonneg (Nat.cast_nonneg (α := ℝ) B)
    (mul_nonneg hΛpos hlogpos)
  nlinarith only [hscaled, hlogscaled, hΛ, hB]

theorem baselineDensityCoefficient_bound (B d : ℕ) (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log d) (hΛ : 1 ≤ baselineHostMultiplier d) :
    2048 * baselineHostMultiplier d * Real.log ((d ^ B : ℕ) + 1) + 5 / 2 ≤
      baselineTargetDensity B d :=
  polynomialDensityCoefficient_bound B d (baselineHostMultiplier d) hd hlog hΛ

theorem baseline_target_density_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B d : ℕ) (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log d) (hΛ : 1 ≤ baselineHostMultiplier d)
    (hmax : ∀ v, G.degree v ≤ d ^ B)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard)
    (S : Finset V) :
    ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ baselineTargetDensity B d * S.card := by
  have hbase := global_induced_density_bound G (d ^ B) (Nat.one_le_pow B d hd) hmax
    (baselineHostMultiplier d) (by linarith) hRamsey S
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (baselineDensityCoefficient_bound B d hd hlog hΛ) (Nat.cast_nonneg _))

theorem baseline_subgraph_density_bound {U V : Type*}
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (F : SimpleGraph U) [DecidableRel F.Adj] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hFG : F.IsContained G) (B d : ℕ) (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log d) (hΛ : 1 ≤ baselineHostMultiplier d)
    (hmax : ∀ v, G.degree v ≤ d ^ B)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard) :
    (F.edgeSet.ncard : ℝ) ≤ baselineTargetDensity B d * Fintype.card U := by
  have hbase := global_subgraph_density_bound F G hFG (d ^ B) (Nat.one_le_pow B d hd)
    hmax (baselineHostMultiplier d) (by linarith) hRamsey
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (baselineDensityCoefficient_bound B d hd hlog hΛ) (Nat.cast_nonneg _))

theorem baselineDegreeCutoff_bounds (B d : ℕ) (hd : 8 ≤ d)
    (hΛ₀ : 1 ≤ baselineHostMultiplier d) (hΛ₁ : baselineHostMultiplier d ≤ d)
    (hpower : d ≤ d ^ B) :
    d ≤ baselineDegreeCutoff B d ∧ baselineDegreeCutoff B d ≤ d ^ (B + 3) := by
  have hdreal : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpow : (d : ℝ) ≤ (d : ℝ) ^ B := by exact_mod_cast hpower
  have hp1 : (1 : ℝ) ≤ (d : ℝ) ^ B := by linarith
  have hlower : 32 * baselineHostMultiplier d * (d ^ B : ℕ) ≤
      (baselineDegreeCutoff B d : ℝ) := Nat.le_ceil _
  have hupper : (baselineDegreeCutoff B d : ℝ) ≤
      32 * baselineHostMultiplier d * (d ^ B : ℕ) + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ 32 * baselineHostMultiplier d * (d ^ B : ℕ) by positivity)).le
  have hsmall : (d : ℝ) ≤ baselineDegreeCutoff B d := by
    have h := mul_le_mul_of_nonneg_right hΛ₀ (show (0 : ℝ) ≤ (d ^ B : ℕ) by positivity)
    push_cast at hlower h
    nlinarith
  have hquad : (64 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hcubic := mul_le_mul_of_nonneg_right hquad (show (0 : ℝ) ≤ d by positivity)
  have hpoly : 32 * (d : ℝ) + 1 ≤ (d : ℝ) ^ 3 := by nlinarith
  have hlarge := mul_le_mul_of_nonneg_right hpoly (show 0 ≤ (d : ℝ) ^ B by positivity)
  have hΛscaled := mul_le_mul_of_nonneg_right hΛ₁ (show 0 ≤ (d : ℝ) ^ B by positivity)
  have hbig : (baselineDegreeCutoff B d : ℝ) ≤ (d : ℝ) ^ (B + 3) := by
    rw [pow_add]
    push_cast at hupper
    nlinarith only [hlarge, hΛscaled, hupper, hp1]
  exact ⟨by exact_mod_cast hsmall, by exact_mod_cast hbig⟩

/-- The cheap-host assumptions provide both a polynomial degree bound
and a uniform induced-density bound after a controlled deletion. -/
theorem baseline_bounded_sparse_host {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (B d : ℕ) (hd : 8 ≤ d) (hlog : 1 ≤ Real.log d)
    (hΛ₀ : 1 ≤ baselineHostMultiplier d) (hΛ₁ : baselineHostMultiplier d ≤ d)
    (hpower : d ≤ d ^ B) (hmax : ∀ v, G.degree v ≤ d ^ B)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard)
    (hhost : (H.edgeFinset.card : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard) :
    ∃ J : SimpleGraph W, J ≤ H ∧ (∀ w, (J.neighborSet w).ncard ≤ d ^ (B + 3)) ∧
      (∀ S : Finset W, (J.induce (S : Set W)).edgeSet.ncard ≤ baselineDensityCutoff B d * S.card) ∧
      ∀ f : G.Copy H, ((copyRawEdges f ∩ (H \ J).edgeSet.toFinite.toFinset).card : ℝ) ≤
        (G.edgeSet.ncard : ℝ) / 8 := by
  have hΛ : 0 ≤ baselineHostMultiplier d := by linarith
  have hσ : 0 ≤ baselineTargetDensity B d := by unfold baselineTargetDensity; positivity
  have hdegree : 32 * baselineHostMultiplier d * (d ^ B : ℕ) ≤
      ((baselineDegreeCutoff B d + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil (32 * baselineHostMultiplier d * (d ^ B : ℕ))
    simp only [baselineDegreeCutoff, Nat.cast_add, Nat.cast_one]
    linarith
  have hdensity : 32 * baselineHostMultiplier d * baselineTargetDensity B d ≤
      ((baselineDensityCutoff B d + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil (32 * baselineHostMultiplier d * baselineTargetDensity B d)
    simp only [baselineDensityCutoff, Nat.cast_add, Nat.cast_one]
    linarith
  obtain ⟨J, hJH, hJdegree, hJdensity, hJcost⟩ := bounded_sparse_host_pruning G H (d ^ B)
    (baselineDegreeCutoff B d) (baselineDensityCutoff B d) (baselineTargetDensity B d)
    (baselineHostMultiplier d) hmax hσ
    (baseline_target_density_bound G B d (by omega) hlog hΛ₀ hmax hRamsey) hhost hdegree hdensity
  refine ⟨J, hJH, ?_, hJdensity, hJcost⟩
  intro w
  exact (hJdegree w).trans (baselineDegreeCutoff_bounds B d hd hΛ₀ hΛ₁ hpower).2

end Erdos911
