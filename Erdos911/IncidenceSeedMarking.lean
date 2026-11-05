import Erdos911.IncidenceResidualParameters
import Erdos911.IncidenceCandidateLists
import Erdos911.UniformSeedMarking
import Erdos911.NearRegularMatchingParameters
import Erdos911.BaselineResidualParameters

namespace Erdos911

noncomputable def incidenceCandidateVertices {W : Type*} [Fintype W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (high : Finset W) (A : ℕ) (P d : ℝ) : Finset W := by
  classical
  exact Finset.univ.filter (fun x => x ∉ high ∧ incidenceCommonCutoff A P d ≤ (J.degree x : ℝ))

theorem mem_incidenceCandidateVertices {W : Type*} [Fintype W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (high : Finset W) (A : ℕ) (P d : ℝ) (x : W) :
    x ∈ incidenceCandidateVertices J high A P d ↔
      x ∉ high ∧ incidenceCommonCutoff A P d ≤ (J.degree x : ℝ) := by
  classical
  simp only [incidenceCandidateVertices, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def incidenceMatchingSeeds {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (right : Finset V) (high : Finset W)
    (d s r q m : ℕ) (p τ T : ℝ) : Finset (SeedDescription F H s) := by
  classical
  let L := incidenceCandidateList F H J right high d s p τ
  exact Finset.univ.filter (fun c => (∀ v, (L c v).card ≤ q) ∧
    m ≤ (matchedRoles (maximumListMatching (fun v : thickCandidateRoles J (L c) r T => L c v.val))).card)

theorem mem_incidenceMatchingSeeds {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (right : Finset V) (high : Finset W)
    (d s r q m : ℕ) (p τ T : ℝ) (c : SeedDescription F H s) :
    c ∈ incidenceMatchingSeeds F H J right high d s r q m p τ T ↔
      (∀ v, (incidenceCandidateList F H J right high d s p τ c v).card ≤ q) ∧
      m ≤ (matchedRoles (maximumListMatching (fun v : thickCandidateRoles J
        (incidenceCandidateList F H J right high d s p τ c) r T =>
          incidenceCandidateList F H J right high d s p τ c v.val))).card := by
  classical
  simp only [incidenceMatchingSeeds, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A single family of tuple marks handles every sufficiently large
incidence matching. Root counts use the global degree `D`; the cost uses
the local low-side degree `P`. -/
theorem incidence_seed_marks (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W : Type*) [Fintype W] [DecidableEq W],
    ∀ k D P : ℕ, d ≤ k → d ≤ D → D ≤ d ^ A → d ≤ P →
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
      (right : Finset (Fin k)) (high : Finset W),
    J ≤ H → (∀ v, F.degree v ≤ D) → (∀ w, H.degree w ≤ D) →
    (∀ w, w ∉ high → H.degree w ≤ P) →
    (∀ U V : Finset W, U.card = nearRegularBlockSize d → V.card = nearRegularBlockSize d →
      Disjoint U V → (crossEdges J U V : ℝ) ≤
        nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) →
    let L := incidenceCandidateList F H J right high d (tolerantSamplingSeed A d k)
      (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d)
    let C := incidenceMatchingSeeds F H J right high d (tolerantSamplingSeed A d k)
      (tolerantTupleOrder d) (baselineBlockSize d) (nearRegularMatchingSize d k)
      (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) (incidenceCommonCutoff A P d)
    let X := incidenceCandidateVertices J high A P d
    ∃ marks : (Fin 32 × (Fin (incidenceTupleOrder A) → W)) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (L c.val) (tolerantTupleOrder d)
        (incidenceCommonCutoff A P d) (boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d)) 32
          (nearRegularExceptionBound d k)) ∧
      (∑ e, if marks e = true then
        ((boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d) e.2).card : ℝ) else 0) ≤
          (2 * incidenceTupleMarkRate A P d) * 32 * X.card * (P : ℝ) ^ incidenceTupleOrder A := by
  classical
  obtain ⟨dS, hdS⟩ := tolerant_sampling_parameters_uniform A
  obtain ⟨dE, hdE⟩ := uniform_seed_marking_for_lists A 32 (incidenceTupleOrder A) (by norm_num)
  obtain ⟨dC, hdC⟩ := tuple_center_parameters_uniform (incidenceLossPower A)
  obtain ⟨dI, hdI⟩ := tuple_initial_contraction_uniform (incidenceTupleOrder A)
  obtain ⟨dR, hdR⟩ := incidence_residual_parameters_uniform A
  obtain ⟨dP, hdP⟩ := incidence_tuple_probability_uniform A
  obtain ⟨dB, hdB⟩ := eventually_baseline_residual_bounds A
  obtain ⟨dM, hdM⟩ := near_regular_matching_parameters_uniform
  refine ⟨max dM (max dB (max dS (max dE (max dC (max dI (max dR dP)))))), ?_⟩
  intro d hd W _ _ k D P hdk hdD hDpow hPd F _ H J _ _ right high hJ hF hhost hlocal hnodense
  let L := incidenceCandidateList F H J right high d (tolerantSamplingSeed A d k)
    (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d)
  let C := incidenceMatchingSeeds F H J right high d (tolerantSamplingSeed A d k)
    (tolerantTupleOrder d) (baselineBlockSize d) (nearRegularMatchingSize d k)
    (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) (incidenceCommonCutoff A P d)
  let X := incidenceCandidateVertices J high A P d
  let B : (Fin (incidenceTupleOrder A) → W) → Finset W := boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d)
  obtain ⟨hd1, _, _, he, _, _, hr, _, _, _, _⟩ := hdS d (by omega) D k hdD hDpow hdk
  obtain ⟨_, _, _, _, _, _, hq₁, hq₁small⟩ := hdB d (by omega)
  have hq₁d : baselineBlockSize d ≤ d := by
    exact_mod_cast (show (baselineBlockSize d : ℝ) ≤ d by linarith)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  have hτ : 0 < 1 - 4 * tolerantSamplingError d := by linarith
  have hdegree : ∀ w, J.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE J H hJ).degree_le w).trans (hhost w)
  have hlow : ∀ w, w ∉ high → J.degree w ≤ P := fun w hw =>
    ((SimpleGraph.Copy.ofLE J H hJ).degree_le w).trans (hlocal w hw)
  obtain ⟨_, htheta, hthetaHalf, hcenter⟩ := hdC d (by omega) P hPpos
  have hcontract := hdI d (by omega)
  obtain ⟨hq, hqd, hT, _, hR, hRT, hqR, hrho, hgap, hsupply⟩ := hdR d (by omega) D P
    (by exact_mod_cast hdD) (by exact_mod_cast hDpow) (by exact_mod_cast hPd)
  obtain ⟨hp, hp1, hbeta, hprobability⟩ := hdP d (by omega) P hP1
  obtain ⟨hu, hexponent⟩ := hdM d (by omega) k hdk
  have hqpos : 0 < nearRegularBlockSize d := by omega
  have hsize : ∀ c : C, ∀ v, (L c.val v).card ≤ baselineBlockSize d := fun c =>
    ((mem_incidenceMatchingSeeds F H J right high _ _ _ _ _ _ _ _ c.val).mp c.property).1
  have hmass : ∀ c : C, nearRegularMatchingSize d k ≤ (matchedRoles (maximumListMatching (fun v :
      thickCandidateRoles J (L c.val) (tolerantTupleOrder d) (incidenceCommonCutoff A P d) => L c.val v.val))).card :=
    fun c => ((mem_incidenceMatchingSeeds F H J right high _ _ _ _ _ _ _ _ c.val).mp c.property).2
  have hlocalX : ∀ x ∈ X, J.degree x ≤ P := by
    intro x hx
    exact hlow x ((mem_incidenceCandidateVertices J high A P d x).mp hx).1
  have hQ : ∀ x ∈ X, (highCodegreeGraph J (incidencePairCutoff A P d)).degree x < nearRegularBlockSize d := by
    intro x hx
    apply highCodegreeGraph_degree_lt J (nearRegularBlockSize d) P (incidencePairCutoff A P d)
      (nearRegularRectangleDensity d) hqpos hrho hqR hgap hnodense x
    have heq : neighbors J x = J.neighborFinset x := by
      ext w
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and, J.mem_neighborFinset]
    rw [heq, J.card_neighborFinset_eq_degree]
    exact_mod_cast hlocalX x hx
  have hsingle : ∀ x ∈ X, ((commonCenters J.Adj {x}).card : ℝ) ≤ P := by
    intro x hx
    have heq : commonCenters J.Adj {x} = J.neighborFinset x := by
      ext w
      simp only [mem_commonCenters_iff, Finset.mem_singleton, forall_eq, J.mem_neighborFinset]
    rw [heq, J.card_neighborFinset_eq_degree]
    exact_mod_cast hlocalX x hx
  have hLX : ∀ c : C, ∀ v : thickCandidateRoles J (L c.val) (tolerantTupleOrder d)
      (incidenceCommonCutoff A P d), L c.val v.val ⊆ X := by
    intro c v w hw
    apply (mem_incidenceCandidateVertices J high A P d w).mpr
    exact ⟨((mem_incidenceCandidateList F H J right high _ _ _ _ c.val v.val w).mp hw).2.2.2.2.1,
      thick_candidate_neighbor_degree J (L c.val) _ _ (by omega) v w hw⟩
  have hevent (c : C) :
      (bitProductMeasure (Fin 32 × (Fin (incidenceTupleOrder A) → W))
        (incidenceTupleMarkRate A P d) hp.le hp1).real
      (thickMatchingEvent J (L c.val) (tolerantTupleOrder d) (incidenceCommonCutoff A P d) B 32
        (nearRegularExceptionBound d k)) ≤ Real.exp (-seedEventExponent d k) := by
    apply (thickMatchingEvent_probability J X (L c.val) (tolerantTupleOrder d)
      (incidenceTupleOrder A) D (nearRegularBlockSize d) 31 (nearRegularMatchingSize d k)
      P (incidenceCommonCutoff A P d) (incidencePairCutoff A P d) (tupleContraction d)
      (incidenceTupleMarkRate A P d) (nearRegularRoundSuccess d) (nearRegularExceptionBound d k)
      hr (incidenceTupleOrder_pos A) hqpos (hLX c) hPpos hT hR.le hRT hdegree hsingle hQ hsupply
      hcenter htheta.le hthetaHalf hp.le hp1 hbeta.le hprobability (fun v =>
        (mul_le_mul_of_nonneg_left (show ((L c.val v.val).card : ℝ) ≤ baselineBlockSize d by
          exact_mod_cast hsize c v.val) (by positivity)).trans hcontract)
      (hmass c) hu).trans
    exact Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hexponent)
  obtain ⟨marks, hmarks, hcost⟩ := hdE d (by omega) W (Fin (incidenceTupleOrder A) → W)
    k D hdk hdD hDpow F H J hJ hF hhost (baselineBlockSize d) (nearRegularBlockSize d)
    (tolerantTupleOrder d) (by omega) hq hq₁d hqd (1 / ((tolerantSamplingSeed A d k : ℝ) + 1))
    (incidenceCommonCutoff A P d) (incidenceTupleMarkRate A P d) (seedEventExponent d k)
    (nearRegularExceptionBound d k) hp.le hp1 (by positivity) le_rfl L
    (fun c v => incidenceCandidateList_subset_seedCandidateList F H J right high _ _ _ _ hτ c v)
    C B (fun z => boundedNeighborhoodTupleBlock_card_le J X _ z) hsize
    (fun _ _ w _ => boundedNeighborhoodTupleBlock_incidence_le J X _ (incidenceTupleOrder A) D hdegree w)
    hevent (fun e => ((B e.2).card : ℝ)) (fun _ => Nat.cast_nonneg _)
  refine ⟨marks, hmarks, hcost.trans ?_⟩
  calc
    _ ≤ (2 * incidenceTupleMarkRate A P d) * ((32 : ℝ) * X.card * (P : ℝ) ^ incidenceTupleOrder A) :=
      mul_le_mul_of_nonneg_left (boundedNeighborhoodTupleBlock_round_size_on J X _
        (incidenceTupleOrder A) P 32 hlocalX) (by positivity)
    _ = _ := by ring

end Erdos911
