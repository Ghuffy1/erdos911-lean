import Erdos911.NearRegularResidualParameters
import Erdos911.NearRegularStarBudget
import Erdos911.UniformSeedMarking
import Erdos911.SeedMatchingObstruction
import Erdos911.BaselineResidualParameters
import Erdos911.NearRegularMatchingParameters

namespace Erdos911

noncomputable def nearRegularCandidateVertices {W : Type*} [Fintype W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (D d : ℝ) : Finset W := by
  classical
  exact Finset.univ.filter (fun x => nearRegularCommonCutoff D d ≤ (J.degree x : ℝ))

theorem mem_nearRegularCandidateVertices {W : Type*} [Fintype W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (D d : ℝ) (x : W) :
    x ∈ nearRegularCandidateVertices J D d ↔ nearRegularCommonCutoff D d ≤ (J.degree x : ℝ) := by
  classical
  simp only [nearRegularCandidateVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- All geometric and local-lemma parameters are discharged here. The
remaining hypotheses quantify the matching mass and exceptional roles. -/
theorem near_regular_seed_marking_uniform :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W : Type*) [Fintype W] [DecidableEq W],
    ∀ k D : ℕ, d ≤ k → d ≤ D → D ≤ d ^ 3 →
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj],
    J ≤ H → (∀ v, F.degree v ≤ D) → (∀ w, H.degree w ≤ D) →
    (∀ A B : Finset W, A.card = nearRegularBlockSize d → B.card = nearRegularBlockSize d →
      Disjoint A B → (crossEdges J A B : ℝ) ≤
        nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) →
    ∀ (m : ℕ) (u : ℝ), u ≤ nearRegularRoundSuccess d ^ 32 * m / 2 →
    seedEventExponent d k ≤ nearRegularRoundSuccess d ^ 32 * m / (8 * (nearRegularBlockSize d * nearRegularBlockSize d : ℕ)) →
    let L := unseededCandidateList F H J (tolerantSamplingSeed 3 d k) (1 - 4 * tolerantSamplingError d)
    let C := largeMatchingSeeds F H J (tolerantSamplingSeed 3 d k) (tolerantTupleOrder d)
      (baselineBlockSize d) m (1 - 4 * tolerantSamplingError d) (nearRegularCommonCutoff D d)
    let X := nearRegularCandidateVertices J D d
    ∃ marks : (Fin 32 × (Fin 128 → W)) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (L c.val) (tolerantTupleOrder d)
        (nearRegularCommonCutoff D d) (boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d)) 32 u) ∧
      (∑ e, if marks e = true then ((boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d) e.2).card : ℝ) else 0) ≤
        (2 * nearRegularTupleMarkRate D d) * 32 * X.card * (D : ℝ) ^ 128 := by
  classical
  obtain ⟨dS, hdS⟩ := tolerant_sampling_parameters_uniform 3
  obtain ⟨dE, hdE⟩ := uniform_tolerant_seed_marking 3 32 128 (by norm_num)
  obtain ⟨dC, hdC⟩ := tuple_center_parameters_uniform nearRegularLossPower
  obtain ⟨dI, hdI⟩ := tuple_initial_contraction_uniform 128
  obtain ⟨dR, hdR⟩ := near_regular_residual_parameters_uniform
  obtain ⟨dP, hdP⟩ := near_regular_tuple_probability_uniform
  obtain ⟨dB, hdB⟩ := eventually_baseline_residual_bounds 3
  refine ⟨max dB (max dS (max dE (max dC (max dI (max dR dP))))), ?_⟩
  intro d hd W _ _ k D hdk hdD hDpow F _ H J _ _ hJ hF hhost hnodense m u hu hexponent
  let L := unseededCandidateList F H J (tolerantSamplingSeed 3 d k) (1 - 4 * tolerantSamplingError d)
  let C := largeMatchingSeeds F H J (tolerantSamplingSeed 3 d k) (tolerantTupleOrder d)
    (baselineBlockSize d) m (1 - 4 * tolerantSamplingError d) (nearRegularCommonCutoff D d)
  let X := nearRegularCandidateVertices J D d
  let B : (Fin 128 → W) → Finset W := boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d)
  obtain ⟨hd1, _, _, _, _, _, hr, _, _, _, _⟩ := hdS d (by omega) D k hdD hDpow hdk
  obtain ⟨_, _, _, _, _, _, hq₁, hq₁small⟩ := hdB d (by omega)
  have hq₁d : baselineBlockSize d ≤ d := by
    exact_mod_cast (show (baselineBlockSize d : ℝ) ≤ d by linarith)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hdegree : ∀ w, J.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE J H hJ).degree_le w).trans (hhost w)
  obtain ⟨_, htheta, hthetaHalf, hcenter⟩ := hdC d (by omega) D hDpos
  have hcontract := hdI d (by omega)
  obtain ⟨hq, hqd, hT, _, hR, hRT, hqR, hrho, hgap, hsupply⟩ := hdR d (by omega) D
    (by exact_mod_cast hdD) (by exact_mod_cast hDpow)
  obtain ⟨hp, hp1, hbeta, hprobability⟩ := hdP d (by omega) D hD1
  have hqpos : 0 < nearRegularBlockSize d := by omega
  have hsize : ∀ c : C, ∀ v, (L c.val v).card ≤ baselineBlockSize d := fun c =>
    ((mem_largeMatchingSeeds F H J _ _ _ _ _ _ c.val).mp c.property).1
  have hmass : ∀ c : C, m ≤ (matchedRoles (maximumListMatching (fun v :
      thickCandidateRoles J (L c.val) (tolerantTupleOrder d) (nearRegularCommonCutoff D d) => L c.val v.val))).card :=
    fun c => ((mem_largeMatchingSeeds F H J _ _ _ _ _ _ c.val).mp c.property).2
  have hQ : ∀ x ∈ X, (highCodegreeGraph J (nearRegularPairCutoff D d)).degree x < nearRegularBlockSize d := by
    intro x _
    apply highCodegreeGraph_degree_lt J (nearRegularBlockSize d) D (nearRegularPairCutoff D d)
      (nearRegularRectangleDensity d) hqpos hrho hqR hgap hnodense x
    have heq : neighbors J x = J.neighborFinset x := by
      ext w
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and, J.mem_neighborFinset]
    rw [heq, J.card_neighborFinset_eq_degree]
    exact_mod_cast hdegree x
  have hsingle : ∀ x ∈ X, ((commonCenters J.Adj {x}).card : ℝ) ≤ D := by
    intro x _
    have heq : commonCenters J.Adj {x} = J.neighborFinset x := by
      ext w
      simp only [mem_commonCenters_iff, Finset.mem_singleton, forall_eq, J.mem_neighborFinset]
    rw [heq, J.card_neighborFinset_eq_degree]
    exact_mod_cast hdegree x
  have hevent (c : C) : (bitProductMeasure (Fin 32 × (Fin 128 → W)) (nearRegularTupleMarkRate D d) hp.le hp1).real
      (thickMatchingEvent J (L c.val) (tolerantTupleOrder d) (nearRegularCommonCutoff D d) B 32 u) ≤
        Real.exp (-seedEventExponent d k) := by
    apply (thickMatchingEvent_probability J X (L c.val) (tolerantTupleOrder d) 128 D
      (nearRegularBlockSize d) 31 m D (nearRegularCommonCutoff D d) (nearRegularPairCutoff D d)
      (tupleContraction d) (nearRegularTupleMarkRate D d) (nearRegularRoundSuccess d) u
      hr (by norm_num) hqpos (fun v w hw => (mem_nearRegularCandidateVertices J D d w).mpr
        (thick_candidate_neighbor_degree J (L c.val) _ _ (by omega) v w hw))
      hDpos hT hR.le hRT hdegree hsingle hQ hsupply hcenter htheta.le hthetaHalf
      hp.le hp1 hbeta.le hprobability (fun v =>
        (mul_le_mul_of_nonneg_left (show ((L c.val v.val).card : ℝ) ≤ baselineBlockSize d by
          exact_mod_cast hsize c v.val) (by positivity)).trans hcontract)
      (hmass c) hu).trans
    exact Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hexponent)
  obtain ⟨marks, hmarks, hcost⟩ := hdE d (by omega) W (Fin 128 → W) k D hdk hdD hDpow F H J hJ hF hhost
    (baselineBlockSize d) (nearRegularBlockSize d) (tolerantTupleOrder d)
    (by omega) hq hq₁d hqd
    (nearRegularCommonCutoff D d) (nearRegularTupleMarkRate D d) (seedEventExponent d k) u hp.le hp1 le_rfl
    C B (fun z => boundedNeighborhoodTupleBlock_card_le J X _ z) hsize
    (fun _ _ w _ => boundedNeighborhoodTupleBlock_incidence_le J X _ 128 D hdegree w) hevent
    (fun e => ((B e.2).card : ℝ)) (fun _ => Nat.cast_nonneg _)
  refine ⟨marks, hmarks, hcost.trans ?_⟩
  calc
    _ ≤ (2 * nearRegularTupleMarkRate D d) * ((32 : ℝ) * X.card * (D : ℝ) ^ 128) :=
      mul_le_mul_of_nonneg_left (boundedNeighborhoodTupleBlock_round_size J X _ 128 D 32 hdegree)
        (by positivity)
    _ = _ := by ring

/-- The matching size and exceptional-role threshold are fixed functions
of d and k. Every large seed test is avoided by the same tuple marks. -/
theorem near_regular_seed_marks :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W : Type*) [Fintype W] [DecidableEq W],
    ∀ k D : ℕ, d ≤ k → d ≤ D → D ≤ d ^ 3 →
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj],
    J ≤ H → (∀ v, F.degree v ≤ D) → (∀ w, H.degree w ≤ D) →
    (∀ A B : Finset W, A.card = nearRegularBlockSize d → B.card = nearRegularBlockSize d →
      Disjoint A B → (crossEdges J A B : ℝ) ≤
        nearRegularRectangleDensity d * nearRegularBlockSize d * nearRegularBlockSize d) →
    let L := unseededCandidateList F H J (tolerantSamplingSeed 3 d k) (1 - 4 * tolerantSamplingError d)
    let C := largeMatchingSeeds F H J (tolerantSamplingSeed 3 d k) (tolerantTupleOrder d)
      (baselineBlockSize d) (nearRegularMatchingSize d k) (1 - 4 * tolerantSamplingError d)
        (nearRegularCommonCutoff D d)
    let X := nearRegularCandidateVertices J D d
    ∃ marks : (Fin 32 × (Fin 128 → W)) → Bool,
      (∀ c : C, marks ∉ thickMatchingEvent J (L c.val) (tolerantTupleOrder d)
        (nearRegularCommonCutoff D d) (boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d)) 32
          (nearRegularExceptionBound d k)) ∧
      (∑ e, if marks e = true then ((boundedNeighborhoodTupleBlock J X (nearRegularBlockSize d) e.2).card : ℝ) else 0) ≤
        (2 * nearRegularTupleMarkRate D d) * 32 * X.card * (D : ℝ) ^ 128 := by
  obtain ⟨dS, hdS⟩ := near_regular_seed_marking_uniform
  obtain ⟨dM, hdM⟩ := near_regular_matching_parameters_uniform
  refine ⟨max dS dM, ?_⟩
  intro d hd W _ _ k D hdk hdD hDpow F _ H J _ _ hJ hF hhost hnodense
  obtain ⟨hu, hexponent⟩ := hdM d (by omega) k hdk
  exact hdS d (by omega) W k D hdk hdD hDpow F H J hJ hF hhost hnodense
    (nearRegularMatchingSize d k) (nearRegularExceptionBound d k) hu hexponent

end Erdos911
