import Erdos911.BaselineHostBounds

open Filter

namespace Erdos911

noncomputable def entropyAllowance (x : ℝ) : ℝ := 1 / Real.log x

noncomputable def entropyTargetDensity (B : ℕ) (M x : ℝ) : ℝ :=
  4096 * ((B : ℝ) + 1) * (M * x) * Real.log x

noncomputable def entropyHostDensityCutoff (x : ℝ) : ℕ :=
  Nat.ceil (x ^ 2 * (Real.log x) ^ 3)

theorem entropy_target_density_bound {U V : Type*}
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (F : SimpleGraph U) [DecidableRel F.Adj] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hFG : F.IsContained G) (B d : ℕ) (M : ℝ) (hd : 1 ≤ d) (hM : 1 ≤ M)
    (hlog : 1 ≤ Real.log d) (hmax : ∀ v, G.degree v ≤ d ^ B)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * d) * G.edgeSet.ncard) :
    (F.edgeSet.ncard : ℝ) ≤ entropyTargetDensity B M d * Fintype.card U := by
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ : 1 ≤ M * d := by nlinarith
  have hbase := global_subgraph_density_bound F G hFG (d ^ B) (Nat.one_le_pow B d hd)
    hmax (M * d) (by linarith) hRamsey
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (polynomialDensityCoefficient_bound B d (M * d) hd hlog hΛ) (Nat.cast_nonneg _))

theorem entropy_host_pruning_scales (B d : ℕ) (M : ℝ) (hd : 1 ≤ d)
    (hlog : 1 ≤ Real.log d) (hdegree : 32 * M * Real.log d ≤ d)
    (hdensity : 131072 * ((B : ℝ) + 1) * M ^ 2 ≤ Real.log d) :
    32 * (M * d) * (d ^ B : ℕ) ≤ entropyAllowance d * ((d ^ (B + 3) + 1 : ℕ) : ℝ) ∧
      32 * (M * d) * entropyTargetDensity B M d ≤
        entropyAllowance d * ((entropyHostDensityCutoff d + 1 : ℕ) : ℝ) := by
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hLpos : 0 < Real.log d := by linarith
  constructor
  · have hdegree' : 32 * M * Real.log d ≤ (d : ℝ) ^ 2 := hdegree.trans (by nlinarith)
    have hscale := mul_le_mul_of_nonneg_right hdegree' (show 0 ≤ (d : ℝ) ^ (B + 1) by positivity)
    unfold entropyAllowance
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hLpos).mpr
    push_cast
    rw [pow_add]
    rw [pow_succ] at hscale
    nlinarith only [hscale]
  · have hscale := mul_le_mul_of_nonneg_right hdensity
      (show 0 ≤ (d : ℝ) ^ 2 * (Real.log d) ^ 2 by positivity)
    have hceil := Nat.le_ceil ((d : ℝ) ^ 2 * (Real.log d) ^ 3)
    unfold entropyAllowance entropyTargetDensity entropyHostDensityCutoff
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hLpos).mpr
    push_cast
    nlinarith only [hscale, hceil]

theorem eventually_entropy_host_parameters (B : ℕ) (M : ℝ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, 131072 ≤ d ∧ 32768 ≤ Real.log d ∧
      1 ≤ Real.log (Real.log d) ∧ M ≤ d ∧ 32 * M * Real.log d ≤ d ∧
      131072 * ((B : ℝ) + 1) * M ^ 2 ≤ Real.log d := by
  have hp := (biased_probability_tends_to_zero (32 * M)).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hl := Real.tendsto_log_atTop.eventually (eventually_ge_atTop
    (max 32768 (131072 * ((B : ℝ) + 1) * M ^ 2)))
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hl.and (hll.and (hp.and (eventually_ge_atTop M))))
  refine ⟨max 131072 (Nat.ceil x₀), ?_⟩
  intro d hd
  have hdlarge : 131072 ≤ d := (le_max_left _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hx : x₀ ≤ (d : ℝ) := (Nat.le_ceil x₀).trans
    (by exact_mod_cast (le_max_right 131072 (Nat.ceil x₀)).trans hd)
  obtain ⟨hlog, hloglog, hrate, hMd⟩ := hx₀ d hx
  have hdegree : 32 * M * Real.log d ≤ d := by
    have h := (div_lt_iff₀ hdpos).mp hrate
    linarith
  exact ⟨hdlarge, (le_max_left _ _).trans hlog, hloglog, hMd, hdegree, (le_max_right _ _).trans hlog⟩

theorem entropy_bounded_sparse_host {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph W) [DecidableRel K.Adj]
    (B d : ℕ) (M : ℝ) (hd : 1 ≤ d) (hM : 1 ≤ M) (hlog : 1 ≤ Real.log d)
    (hdegree : 32 * M * Real.log d ≤ d)
    (hdensity : 131072 * ((B : ℝ) + 1) * M ^ 2 ≤ Real.log d)
    (hmax : ∀ v, G.degree v ≤ d ^ B)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * d) * G.edgeSet.ncard)
    (hhost : (K.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard) :
    ∃ H : SimpleGraph W, H ≤ K ∧ (∀ w, (H.neighborSet w).ncard ≤ d ^ (B + 3)) ∧
      (∀ S : Finset W, (H.induce (S : Set W)).edgeSet.ncard ≤ entropyHostDensityCutoff d * S.card) ∧
      ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeSet.toFinite.toFinset).card : ℝ) ≤
        entropyAllowance d * G.edgeSet.ncard / 8 := by
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hΛ : 1 ≤ M * d := by nlinarith
  have hσ : 0 ≤ entropyTargetDensity B M d := by unfold entropyTargetDensity; positivity
  have hlocal : ∀ S : Finset V,
      ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ entropyTargetDensity B M d * S.card := by
    intro S
    have h := entropy_target_density_bound (G.induce (S : Set V)) G
      ⟨SimpleGraph.Copy.induce G (S : Set V)⟩ B d M hd hM hlog hmax hRamsey
    have hcard : Fintype.card (S : Set V) = S.card := by simp
    simpa only [hcard] using h
  obtain ⟨hD, hT⟩ := entropy_host_pruning_scales B d M hd hlog hdegree hdensity
  exact bounded_sparse_host_pruning_scaled G K (d ^ B) (d ^ (B + 3))
    (entropyHostDensityCutoff d) (entropyTargetDensity B M d) (M * d) (entropyAllowance d)
    hmax hσ hlocal hhost hD hT

end Erdos911
