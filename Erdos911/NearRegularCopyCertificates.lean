import Erdos911.NearRegularCertificateEstimates
import Erdos911.NearRegularSeedMarking
import Erdos911.BaselineResidualParameters

open Filter

namespace Erdos911

theorem degree_edge_count_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d Δ : ℕ)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ) :
    (d : ℝ) * Fintype.card V / 2 ≤ G.edgeSet.ncard ∧
      (G.edgeSet.ncard : ℝ) ≤ (Δ : ℝ) * Fintype.card V / 2 := by
  classical
  have hlo : d * Fintype.card V ≤ ∑ v : V, G.degree v := by
    calc
      _ = ∑ _v : V, d := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hmin v)
  have hhi : (∑ v : V, G.degree v) ≤ Δ * Fintype.card V := by
    calc
      _ ≤ ∑ _v : V, Δ := Finset.sum_le_sum (fun v _ => hmax v)
      _ = _ := by simp [Nat.mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges, G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hlo hhi
  have hloR : (d : ℝ) * Fintype.card V ≤ 2 * G.edgeSet.ncard := by exact_mod_cast hlo
  have hhiR : (2 : ℝ) * G.edgeSet.ncard ≤ (Δ : ℝ) * Fintype.card V := by exact_mod_cast hhi
  constructor <;> linarith

/-- A star-deficit-free copy with the prescribed edge-loss allowance
produces a seed in the family used by the uniform marking theorem. -/
theorem near_regular_copy_certificate_uniform (A B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W : Type*) [Fintype W] [DecidableEq W],
    ∀ k D Δ : ℕ,
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj],
    F.Connected → J ≤ H → (∀ v, d ≤ F.degree v) → (∀ v, F.degree v ≤ Δ) → Δ ≤ D →
    (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower → D ≤ d ^ 3 →
    (∀ w, H.degree w ≤ D) →
    (∀ U V : Finset W, U.card = baselineBlockSize d → V.card = baselineBlockSize d →
      Disjoint U V → (crossEdges J U V : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) →
    ∀ f : F.Copy H,
    ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) (tolerantTupleOrder d) D
      ((F.edgeSet.ncard : ℝ) / 32 * Real.log ((D : ℝ) / nearRegularCommonCutoff D d)) →
    ((F \ copyRetainedGraph J f).edgeSet.ncard : ℝ) ≤ nearRegularLossFraction B d * F.edgeSet.ncard →
    ∃ c ∈ largeMatchingSeeds F H J (tolerantSamplingSeed 3 d k) (tolerantTupleOrder d)
      (baselineBlockSize d) (nearRegularMatchingSize d k) (1 - 4 * tolerantSamplingError d)
        (nearRegularCommonCutoff D d), ∃ E : Finset (Fin k),
      (E.card : ℝ) ≤ nearRegularExceptionBound d k ∧
      ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J (tolerantSamplingSeed 3 d k)
        (1 - 4 * tolerantSamplingError d) c v := by
  obtain ⟨dE, hdE⟩ := near_regular_certificate_estimates_uniform A B hB
  obtain ⟨dS, hdS⟩ := tolerant_sampling_parameters_uniform 3
  obtain ⟨dQ, hdQ⟩ := eventually_baseline_residual_bounds 3
  obtain ⟨dR, hdR⟩ := near_regular_residual_parameters_uniform
  obtain ⟨xε, hxε⟩ := eventually_atTop.mp (tolerantSamplingError_tends_to_zero.eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 20 by norm_num)))
  refine ⟨max 1 (max dE (max dS (max dQ (max dR (Nat.ceil xε))))), ?_⟩
  intro d hd W _ _ k D Δ F _ H J _ _ hF hJ hmin hmax hΔD hdegree hDpow hhost hnodense f hgood hloss
  have hd1 : 1 ≤ d := by omega
  have hdpos : 0 < d := by omega
  have hdReal : (0 : ℝ) < d := by exact_mod_cast hdpos
  obtain ⟨v⟩ := hF.nonempty
  have hdk : d ≤ k := by
    simpa only [Fintype.card_fin] using (hmin v).trans (F.degree_lt_card_verts v).le
  have hdD : d ≤ D := (hmin v).trans ((hmax v).trans hΔD)
  have hΔpos : 0 < Δ := hdpos.trans_le ((hmin v).trans (hmax v))
  have hmaxD : ∀ v, F.degree v ≤ D := fun v => (hmax v).trans hΔD
  obtain ⟨_, hlog, hεpos, hε, hαpos, hα, _, htuple, _, hseedBound, hseed⟩ :=
    hdS d (by omega) D k hdD hDpow hdk
  obtain ⟨_, _, _, _, _, _, hq, hqsmall⟩ := hdQ d (by omega)
  obtain ⟨_, _, hT, hTD, _⟩ := hdR d (by omega) D (by exact_mod_cast hdD) (by exact_mod_cast hDpow)
  have hεsmall : tolerantSamplingError d < 1 / 20 := hxε d
    ((Nat.le_ceil xε).trans (by exact_mod_cast (show Nat.ceil xε ≤ d by omega)))
  have hsmall : 2 * baselineBlockSize d ≤ d := by
    exact_mod_cast (show (2 : ℝ) * baselineBlockSize d ≤ d by linarith)
  have hgap : (1 / 4 : ℝ) * d + baselineBlockSize d < (1 - 5 * tolerantSamplingError d) * d := by
    nlinarith only [hqsmall, hεsmall, hdReal]
  obtain ⟨hlo, hhi⟩ := degree_edge_count_bounds F d Δ hmin hmax
  simp only [Fintype.card_fin] at hlo hhi
  obtain ⟨hmass, hexception, hcost⟩ := hdE d (by omega) k Δ F.edgeSet.ncard
    (F \ copyRetainedGraph J f).edgeSet.ncard (tolerantSamplingSeed 3 d k)
    (Nat.cast_nonneg _) hdegree hlo hhi hloss hseedBound
  exact tolerant_copy_matching_certificate F H J hF hJ f d D Δ (tolerantSamplingSeed 3 d k)
    (baselineBlockSize d) (tolerantTupleOrder d) D (nearRegularMatchingSize d k) hdpos hmin hmaxD hmax
    hΔpos hhost hq hsmall (by omega) (1 / 4) (tolerantSamplingRate 3 d) (tolerantSamplingError d)
    (nearRegularCommonCutoff D d) (nearRegularExceptionBound d k) (by norm_num) hαpos
    (by linarith) hεpos hε hT hTD hgap hnodense hseed (by linarith) hgood hcost hmass hexception

end Erdos911
