import Erdos911.BandSubtargets
import Erdos911.BranchRamseyGeneral

namespace Erdos911

/-- The low part of a large band satisfies the near-regular theorem,
with isolated vertices removed and no loss of edges. -/
theorem low_band_ramsey_bound (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ v ∈ G.support, (q : ℝ) / 65536 ≤ G.degree v) →
      (∀ v, (G.degree v : ℝ) ≤ bandLeftThreshold q + 2 * q) →
      (∀ S : Finset V, S.card ≤ 2 * nearRegularBlockSize (bandDegree q) →
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ C * Real.log (bandDegree q) * S.card) →
      (M * bandDegree q) * G.edgeSet.ncard ≤ (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨qP, hP⟩ := band_parameters_uniform 0
  obtain ⟨dR, hR⟩ := near_regular_size_ramsey_lower_bound_general 524288 M C (by norm_num) hM hC
  refine ⟨max qP (65536 * dR), ?_⟩
  intro q hq V _ _ G _ hmin hmax hlocal
  classical
  obtain ⟨_, _, _, _, _, hlow, _⟩ := hP q ((le_max_left _ _).trans hq)
  have hdR : dR ≤ bandDegree q := by unfold bandDegree; omega
  by_cases he : 0 < G.edgeSet.ncard
  · let J := G.induce G.support
    have hcard := support_card_pos_of_edge_ncard_pos G he
    let : Nonempty G.support := Fintype.card_pos_iff.mp hcard
    have hdegree (v : G.support) : J.degree v = G.degree v.val := degree_induce_support G v
    have hminJ (v : G.support) : bandDegree q ≤ J.degree v := by
      rw [hdegree]
      have hdiv : (bandDegree q : ℝ) ≤ (q : ℝ) / 65536 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 65536)]
        exact_mod_cast Nat.div_mul_le_self q 65536
      exact_mod_cast hdiv.trans (hmin v.val v.property)
    have hmaxJ (v : G.support) : (J.degree v : ℝ) ≤
        524288 * bandDegree q * (Real.log (bandDegree q)) ^ nearRegularDegreePower := by
      rw [hdegree]
      exact (hmax v.val).trans hlow
    obtain ⟨v, hv⟩ := J.exists_maximal_degree_vertex
    have hbound : (J.maxDegree : ℝ) ≤
        524288 * bandDegree q * (Real.log (bandDegree q)) ^ nearRegularDegreePower := by
      rw [hv]
      exact hmaxJ v
    have hlocalJ := induced_density_of_copy (SimpleGraph.Copy.induce G G.support)
      (2 * nearRegularBlockSize (bandDegree q)) (C * Real.log (bandDegree q)) hlocal
    have h := hR (bandDegree q) hdR G.support J.maxDegree J hcard
      (by simpa only [SimpleGraph.ncard_neighborSet] using hminJ)
      (fun v => by simpa only [SimpleGraph.ncard_neighborSet] using J.degree_le_maxDegree v)
      hbound hlocalJ
    have hmono : SimpleGraph.sizeRamsey J J ≤ SimpleGraph.sizeRamsey G G :=
      sizeRamsey_mono ⟨SimpleGraph.Copy.induce G G.support⟩ ⟨SimpleGraph.Copy.induce G G.support⟩
    rw [show J.edgeSet.ncard = G.edgeSet.ncard from edge_ncard_induce_support G] at h
    exact h.le.trans (by exact_mod_cast hmono)
  · have hz : G.edgeSet.ncard = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero]
    exact Nat.cast_nonneg _

/-- The high part has a normalized incidence copy retaining at least
one edge out of 262144, so it inherits the incidence Ramsey bound. -/
theorem high_band_ramsey_bound (B : ℕ) (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], ∀ left right : Finset V,
      G.IsBipartiteWith (left : Set V) (right : Set V) →
      (∀ v ∈ G.support, (q : ℝ) / 65536 ≤ G.degree v) →
      (∀ v, G.degree v ≤ (2 * q) ^ B) →
      (∀ v ∈ right, G.degree v ≤ 2 * q) →
      (∀ v ∈ left, v ∈ G.support → bandLeftThreshold q / 8 < G.degree v) →
      (∀ S : Finset V, S.card ≤ 2 * nearRegularBlockSize (bandDegree q) →
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ C * Real.log (bandDegree q) * S.card) →
      (M * bandDegree q) * G.edgeSet.ncard ≤ 262144 * (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨qP, hP⟩ := band_parameters_uniform B
  obtain ⟨dR, hR⟩ := incidence_size_ramsey_lower_bound_general (B + 1) M C
    (nearRegularDegreePower / 2) hM hC (by norm_num [nearRegularDegreePower])
  refine ⟨max qP (65536 * dR), ?_⟩
  intro q hq V _ _ G _ left right hBip hmin hmax hright hleft hlocal
  classical
  obtain ⟨hqLarge, hd, _, hlog, _, _, hgap, hprob⟩ := hP q ((le_max_left _ _).trans hq)
  obtain ⟨ha, hc⟩ := hprob ((2 * q) ^ B) le_rfl
  have hdR : dR ≤ bandDegree q := by unfold bandDegree; omega
  by_cases he : 0 < G.edgeSet.ncard
  · obtain ⟨S, hSG, hcard, hminJ, hmaxJ, hrightJ, hleftJ, hmass⟩ :=
      exists_high_band_normalization G left right hBip B q ((2 * q) ^ B)
        hqLarge hlog hgap ha hc hmin hmax hright hleft he
    let J := incidenceGraph S
    obtain ⟨f⟩ := hSG
    have hlocalJ := induced_density_of_copy f
      (2 * nearRegularBlockSize (bandDegree q)) (C * Real.log (bandDegree q)) hlocal
    have h := hR (bandDegree q) hdR _ J hcard
      (by simpa only [SimpleGraph.ncard_neighborSet] using hminJ)
      (by simpa only [SimpleGraph.ncard_neighborSet] using hmaxJ) hlocalJ
      (Finset.univ.map Function.Embedding.inl) (Finset.univ.map Function.Embedding.inr)
      (incidenceGraph_bipartite S) (by
        intro v hv
        cases v with
        | inl x => simp at hv
        | inr y => simpa only [SimpleGraph.ncard_neighborSet] using hrightJ y) (by
        intro v hv
        cases v with
        | inl x => simpa only [SimpleGraph.ncard_neighborSet] using hleftJ x
        | inr y => simp at hv)
    have hmono : (SimpleGraph.sizeRamsey J J : ℝ) ≤ SimpleGraph.sizeRamsey G G := by
      exact_mod_cast sizeRamsey_mono ⟨f⟩ ⟨f⟩
    have hnonneg : (0 : ℝ) ≤ M * bandDegree q := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have hscaled := mul_le_mul_of_nonneg_left hmass hnonneg
    nlinarith only [hscaled, h.le.trans hmono]
  · have hz : G.edgeSet.ncard = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero]
    positivity

end Erdos911
