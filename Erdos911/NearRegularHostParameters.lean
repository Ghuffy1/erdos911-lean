import Erdos911.NearRegularCertificateEstimates
import Erdos911.DenseWitnessColoring

open Filter Asymptotics

namespace Erdos911

noncomputable def nearRegularHostCutoff (M : ℝ) (d Δ : ℕ) : ℕ :=
  Nat.ceil (16 * M * d * Δ)

theorem nearRegularHostCutoff_bounds (M : ℝ) (d Δ : ℕ)
    (hM : 1 ≤ M) (hd : 1 ≤ d) (hΔ : 1 ≤ Δ) :
    d ≤ nearRegularHostCutoff M d Δ ∧
      16 * M * d * Δ ≤ (nearRegularHostCutoff M d Δ : ℝ) ∧
      (nearRegularHostCutoff M d Δ : ℝ) ≤ 32 * M * d * Δ := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hΔR : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hMnonneg : 0 ≤ M := by linarith
  have hMd := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg (α := ℝ) d)
  have hproduct := mul_le_mul_of_nonneg_left hΔR (show 0 ≤ M * (d : ℝ) by positivity)
  have hbase : (d : ℝ) ≤ M * d * Δ := by nlinarith only [hMd, hproduct]
  have hlower : 16 * M * d * Δ ≤ (nearRegularHostCutoff M d Δ : ℝ) := Nat.le_ceil _
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 16 * M * d * Δ by positivity)).le
  change (nearRegularHostCutoff M d Δ : ℝ) ≤ 16 * M * d * Δ + 1 at hceil
  refine ⟨?_, hlower, ?_⟩
  · have h : (d : ℝ) ≤ nearRegularHostCutoff M d Δ := by nlinarith only [hbase, hlower, hdR]
    exact_mod_cast h
  · nlinarith only [hceil, hbase, hdR]

theorem near_regular_host_parameters_uniform (A M : ℝ) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ Δ : ℕ, 1 ≤ Δ →
      (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
      d ≤ nearRegularHostCutoff M d Δ ∧
      16 * M * d * Δ ≤ (nearRegularHostCutoff M d Δ : ℝ) ∧
      (nearRegularHostCutoff M d Δ : ℝ) ≤ 32 * M * d * Δ ∧
      nearRegularHostCutoff M d Δ ≤ d ^ 3 := by
  have hratio : Tendsto (fun x : ℝ => 32 * M * A * (Real.log x) ^ nearRegularDegreePower / x)
      atTop (nhds 0) := by
    simpa only [mul_zero, mul_div_assoc, Real.rpow_one] using
      ((isLittleO_log_rpow_rpow_atTop nearRegularDegreePower
        (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero).const_mul (32 * M * A)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    (hratio.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨max 1 (Nat.ceil x₀), ?_⟩
  intro d hd Δ hΔ hdegree
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨hdD, hlower, hupper⟩ := nearRegularHostCutoff_bounds M d Δ hM hd1 hΔ
  have hscale : 32 * M * A * (Real.log d) ^ nearRegularDegreePower ≤ (d : ℝ) := by
    have h := hx₀ d ((Nat.le_ceil x₀).trans (by exact_mod_cast (show Nat.ceil x₀ ≤ d by omega)))
    simpa only [one_mul] using ((div_lt_iff₀ hdpos).mp h).le
  have hMnonneg : 0 ≤ M := by linarith
  have hdegree' := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 32 * M * (d : ℝ) by positivity)
  have hscale' := mul_le_mul_of_nonneg_right hscale (show 0 ≤ (d : ℝ) ^ 2 by positivity)
  have hDpow : (nearRegularHostCutoff M d Δ : ℝ) ≤ (d : ℝ) ^ 3 := by
    nlinarith only [hupper, hdegree', hscale']
  exact ⟨hdD, hlower, hupper, by exact_mod_cast hDpow⟩

theorem near_regular_initial_pruning_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph W) [DecidableRel K.Adj]
    (d Δ D : ℕ) (M : ℝ) (hmax : ∀ v, G.degree v ≤ Δ)
    (hbudget : (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard)
    (hcutoff : 16 * M * d * Δ ≤ (D : ℝ)) (f : G.Copy K) :
    ((copyRawEdges f ∩ (K \ degreePrunedGraph K D).edgeFinset).card : ℝ) ≤
      (G.edgeSet.ncard : ℝ) / 8 := by
  apply (degreePruned_copy_deleted_capacity G K f Δ D hmax).trans
  have hden : (0 : ℝ) < (D + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hden).mpr
  have hb := mul_le_mul_of_nonneg_right hbudget (show 0 ≤ 2 * (Δ : ℝ) by positivity)
  have hs := mul_le_mul_of_nonneg_right hcutoff (Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard)
  rw [K.edgeFinset_card, Set.fintypeCard_eq_ncard]
  push_cast
  nlinarith only [hb, hs, Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard]

end Erdos911
