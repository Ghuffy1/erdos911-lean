import Erdos911.IncidenceSeedMarking
import Erdos911.IncidenceCertificateEstimates
import Erdos911.IncidenceTupleDeficit
import Erdos911.IncidenceOrientation

namespace Erdos911

/-- After the three copy tests, adaptive sampling supplies a certificate
in exactly the seed family handled by the uniform marking theorem. -/
theorem incidence_copy_certificate_uniform (A : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W : Type*) [Fintype W] [DecidableEq W],
    ∀ k D P : ℕ, d ≤ P →
    ∀ (F : SimpleGraph (Fin k)) [DecidableRel F.Adj]
      (H J K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj],
    F.Connected → J ≤ H → H ≤ lowEndpointPrunedGraph K P →
    (∀ v, d ≤ F.degree v) → (∀ v, F.degree v ≤ D) → D ≤ d ^ A →
    (∀ w, H.degree w ≤ D) →
    ∀ right : Finset (Fin k), (∀ v ∈ right, F.degree v ≤ d) →
    F.edgeSet.ncard = d * right.card → k ≤ 2 * right.card →
    (∀ U V : Finset W, U.card = baselineBlockSize d → V.card = baselineBlockSize d →
      Disjoint U V → (crossEdges J U V : ℝ) ≤ (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) →
    ∀ (f : F.Copy H) (removed : Finset (Sym2 W)),
    (∀ x y, H.Adj x y → x ∉ highHostVertices K P → y ∈ highHostVertices K P →
      s(x, y) ∉ removed → J.Adj x y) →
    ((copyRawEdges f ∩ removed).card : ℝ) ≤ nearRegularLossFraction B d * F.edgeSet.ncard →
    (d : ℝ) * (incidenceOrientationDefects F f right (highHostVertices K P) d).card ≤
      (F.edgeSet.ncard : ℝ) / 32 →
    copyRawEdges f ∉ starImagePatterns H J (copyVertices f) (tolerantTupleOrder d)
      F.edgeSet.ncard D P ((F.edgeSet.ncard : ℝ) / 128 *
        Real.log ((P : ℝ) / incidenceCommonCutoff A P d)) →
    ∃ c ∈ incidenceMatchingSeeds F H J right (highHostVertices K P) d (tolerantSamplingSeed A d k)
      (tolerantTupleOrder d) (baselineBlockSize d) (nearRegularMatchingSize d k)
      (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) (incidenceCommonCutoff A P d),
      ∃ E : Finset (Fin k), (E.card : ℝ) ≤ nearRegularExceptionBound d k ∧
        (∀ v, (incidenceCandidateList F H J right (highHostVertices K P) d (tolerantSamplingSeed A d k)
          (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) c v).Nonempty → v ∉ E →
            f v ∈ incidenceCandidateList F H J right (highHostVertices K P) d (tolerantSamplingSeed A d k)
              (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) c v) ∧
        ∀ v, (incidenceCandidateList F H J right (highHostVertices K P) d (tolerantSamplingSeed A d k)
          (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) c v).Nonempty → v ∉ E →
            ∃ u, F.Adj v u ∧ f u ∈ highHostVertices K P := by
  classical
  obtain ⟨dS, hdS⟩ := incidence_sampling_parameters_uniform A
  obtain ⟨dE, hdE⟩ := incidence_certificate_estimate_parameters A B
  obtain ⟨dQ, hdQ⟩ := incidence_first_scale_parameters_uniform
  obtain ⟨dR, hdR⟩ := incidence_residual_parameters_uniform A
  refine ⟨max dS (max dE (max dQ dR)), ?_⟩
  intro d hd W _ _ k D P hdP F _ H J K _ _ _ hF hJ hH hmin hmax hDpow hhost right hright
    hbalance hhalf hnodense f removed hcross hloss horient hgood
  obtain ⟨v⟩ := hF.nonempty
  have hdk : d ≤ k := by
    simpa only [Fintype.card_fin] using (hmin v).trans (F.degree_lt_card_verts v).le
  have hdD : d ≤ D := (hmin v).trans (hmax v)
  obtain ⟨hd1, hlog, hεpos, hε, hp, hp1, hr, htuple, _, hseedBound, hseed⟩ :=
    hdS d (by omega) D k hdD hDpow hdk
  obtain ⟨_, _, hpower, hcoef⟩ := hdE d (by omega)
  obtain ⟨hdpos, hqpos, hqsmall, _, hgap⟩ := hdQ d (by omega)
  obtain ⟨_, _, hT, hTP, _⟩ := hdR d (by omega) D P
    (by exact_mod_cast hdD) (by exact_mod_cast hDpow) (by exact_mod_cast hdP)
  have hPpos : 0 < P := lt_of_lt_of_le hdpos hdP
  have hkpos : 0 < k := lt_of_lt_of_le hdpos hdk
  have hτ : 0 < 1 - 4 * tolerantSamplingError d := by linarith
  have hJdegree : ∀ w, J.degree w ≤ D := fun w =>
    ((SimpleGraph.Copy.ofLE J H hJ).degree_le w).trans (hhost w)
  obtain ⟨c, hagree, hacc⟩ := exists_adaptive_incidence_seed F H J hF f right (highHostVertices K P)
    d D (tolerantSamplingSeed A d k) hdpos hdD hmin hright hJdegree
    (tolerantSamplingRate A d) (tolerantSamplingError d) hp (by linarith) hεpos.le (by linarith) hseed
  let L := incidenceCandidateList F H J right (highHostVertices K P) d (tolerantSamplingSeed A d k)
    (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d) c
  let E := incidenceRetentionDefects F H J f right (highHostVertices K P) d (tolerantSamplingError d)
  let bad := smallCommonNeighborhoodRoles J L (tolerantTupleOrder d) (incidenceCommonCutoff A P d)
  let orient := incidenceOrientationDefects F f right (highHostVertices K P) d
  let matched := matchedRoles (maximumListMatching (fun v :
    thickCandidateRoles J L (tolerantTupleOrder d) (incidenceCommonCutoff A P d) => L v.val))
  have hsize : ∀ v, (L v).card ≤ baselineBlockSize d := fun v =>
    (incidenceCandidateList_card_lt F H J f right (highHostVertices K P) d
      (tolerantSamplingSeed A d k) (baselineBlockSize d) hdpos hqpos hqsmall
      (tolerantSamplingRate A d) (tolerantSamplingError d) (1 / 4) hp (by norm_num)
      hgap hnodense c hacc v).le
  have hbad : (d : ℝ) * bad.card ≤ (F.edgeSet.ncard : ℝ) / 8 :=
    (incidence_small_common_roles_card_bound F H J hJ f right (highHostVertices K P) d
      (tolerantSamplingSeed A d k) (tolerantTupleOrder d) D P hkpos hdpos hPpos
      (incidenceCommonCutoff A P d) (tolerantSamplingRate A d) (tolerantSamplingError d)
      hp hT hTP hhost hεpos.le hε (by linarith only [htuple]) c hacc hgood).le
  have hedge : (F.edgeSet.ncard : ℝ) ≤ (d : ℝ) * k := by
    rw [hbalance, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast (show right.card ≤ k by simpa only [Fintype.card_fin] using Finset.card_le_univ right))
      (Nat.cast_nonneg _)
  obtain ⟨hbudget, hexcept, hmsmall⟩ := incidence_certificate_budgets A B d k F.edgeSet.ncard
    (copyRawEdges f ∩ removed).card (tolerantSamplingSeed A d k) hB
    (by exact_mod_cast hdpos) hlog hedge (Nat.cast_nonneg _) (Nat.cast_nonneg _) hloss hseedBound hcoef hpower
  have hmatching : (right.card : ℝ) ≤ matched.card + bad.card + orient.card +
      (tolerantSamplingSeed A d k : ℝ) +
        8 * ((copyRawEdges f ∩ removed).card : ℝ) / (tolerantSamplingError d * d) :=
    incidence_cross_matching_bound F H J K P hH f right orient removed d
      (tolerantSamplingSeed A d k) (tolerantTupleOrder d) hdpos (tolerantSamplingRate A d)
      (tolerantSamplingError d) (incidenceCommonCutoff A P d) hp hεpos hτ c hagree hacc
      (fun v hv hvO => incidenceOrientationDefects_large_complement F f right (highHostVertices K P) d v hv hvO)
      hcross
  have hmass : nearRegularMatchingSize d k ≤ matched.card :=
    incidence_matching_mass_of_budgets d k matched.card right.card F.edgeSet.ncard bad.card orient.card
      (tolerantSamplingSeed A d k) (8 * ((copyRawEdges f ∩ removed).card : ℝ) / (tolerantSamplingError d * d))
      (by exact_mod_cast hdpos) (by exact_mod_cast hbalance)
      (by
        have h : (k : ℝ) ≤ 2 * right.card := by exact_mod_cast hhalf
        linarith only [h])
      hbad horient hbudget hmatching hmsmall
  have hEbound : (E.card : ℝ) ≤ 4 * ((copyRawEdges f ∩ removed).card : ℝ) /
      (tolerantSamplingError d * d) := by
    apply (le_div_iff₀ (mul_pos hεpos (by exact_mod_cast hdpos))).mpr
    simpa only [E, mul_assoc, mul_comm, mul_left_comm] using
      incidenceRetentionDefects_cross_bound F H J K P hH f right removed d (tolerantSamplingError d) hcross
  refine ⟨c, (mem_incidenceMatchingSeeds F H J right (highHostVertices K P) _ _ _ _ _ _ _ _ c).mpr
    ⟨hsize, hmass⟩, E, hEbound.trans hexcept, ?_, ?_⟩
  · exact incidence_true_image_outside_defects F H J K P hH f right d (tolerantSamplingSeed A d k)
      hdpos (tolerantSamplingRate A d) (tolerantSamplingError d) hp hεpos.le hτ c hagree hacc
  · intro v hne _
    obtain ⟨w, hw⟩ := hne
    exact incidence_candidate_actual_high_neighbor F H J right (highHostVertices K P) d
      (tolerantSamplingSeed A d k) (tolerantSamplingRate A d) (1 - 4 * tolerantSamplingError d)
      hτ c f hagree v w hw

end Erdos911
