import Erdos911.SubsetTupleDeficit
import Erdos911.IncidenceListAccuracy

namespace Erdos911

theorem high_subset_slot_eq_candidateSlice {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (high : Finset W) (v : Fin n) (w : W) :
    subsetSlotNeighbors (copyHighNeighbors F f high v) J f (some w) =
      candidateSlice (copyHighNeighbors F f high v) (fun j => J.neighborFinset (f j)) w := by
  classical
  ext u
  simp only [mem_subsetSlotNeighbors, candidateSlice, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset, Option.some.injEq, forall_eq', J.adj_comm]

/-- The actual adaptive incidence lists force a restricted-star pattern
when too many of their roles contain a small common neighborhood. -/
theorem incidence_small_common_roles_pattern {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (f : F.Copy H)
    (right : Finset (Fin n)) (high : Finset W) (d S r D P : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hP : 0 < P) (T p ε ℓ : ℝ)
    (hp : 0 < p) (hT : 0 < T) (hTP : T ≤ P)
    (hD : ∀ w, H.degree w ≤ D) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 5)
    (hbudget : (r : ℝ) * (5 * ε) ≤ 1 / 2) (c : SeedDescription F H S)
    (hacc : IncidenceSeedAccurate F H J f right high d S p ε c)
    (hmass : 16 * ℓ ≤ (d : ℝ) * (smallCommonNeighborhoodRoles J
      (incidenceCandidateList F H J right high d S p (1 - 4 * ε) c) r T).card *
        Real.log ((P : ℝ) / T)) :
    copyRawEdges f ∈ starImagePatterns H J (copyVertices f) r F.edgeSet.ncard D P ℓ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let L := incidenceCandidateList F H J right high d S p (1 - 4 * ε) c
  let N := copyHighNeighbors F f high
  have hN (v : Fin n) : N v ⊆ F.neighborFinset v := by
    intro u hu
    exact (F.mem_neighborFinset v u).mpr ((mem_copyHighNeighbors F f high v u).mp hu).1
  have hlarge (v : Fin n) (hne : (L v).Nonempty) : d ≤ 4 * (N v).card := by
    obtain ⟨w, hw⟩ := hne
    exact incidence_tested_role_large F H J f right high d S p ε (1 - 4 * ε) hp c hacc v w hw
  have hdense (v : Fin n) (w : W) (hw : w ∈ L v) :
      (1 - 5 * ε) * (N v).card ≤ (subsetSlotNeighbors (N v) J f (some w)).card := by
    rw [high_subset_slot_eq_candidateSlice F H J f high v w]
    exact incidence_candidate_fraction_lower F H J f right high d S hd p ε hp c hacc v w hw
  exact subset_small_common_roles_pattern F H J hJ f L N d r D P T (5 * ε) ℓ
    hd hP hT hTP hD (by positivity) (by linarith) hbudget hN hlarge hdense hmass

theorem incidence_small_common_roles_weighted_bound {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (f : F.Copy H)
    (right : Finset (Fin n)) (high : Finset W) (d S r D P : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hP : 0 < P) (T p ε ℓ : ℝ)
    (hp : 0 < p) (hT : 0 < T) (hTP : T ≤ P)
    (hD : ∀ w, H.degree w ≤ D) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 5)
    (hbudget : (r : ℝ) * (5 * ε) ≤ 1 / 2) (c : SeedDescription F H S)
    (hacc : IncidenceSeedAccurate F H J f right high d S p ε c)
    (hgood : copyRawEdges f ∉ starImagePatterns H J (copyVertices f) r F.edgeSet.ncard D P ℓ) :
    (d : ℝ) * (smallCommonNeighborhoodRoles J
      (incidenceCandidateList F H J right high d S p (1 - 4 * ε) c) r T).card *
        Real.log ((P : ℝ) / T) < 16 * ℓ := by
  apply lt_of_not_ge
  intro h
  exact hgood (incidence_small_common_roles_pattern F H J hJ f right high d S r D P
    hn hd hP T p ε ℓ hp hT hTP hD hε₀ hε₁ hbudget c hacc h)

theorem incidence_small_common_roles_card_bound {n : ℕ} {W : Type*}
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (f : F.Copy H)
    (right : Finset (Fin n)) (high : Finset W) (d S r D P : ℕ)
    (hn : 0 < n) (hd : 0 < d) (hP : 0 < P) (T p ε : ℝ)
    (hp : 0 < p) (hT : 0 < T) (hTP : T < P)
    (hD : ∀ w, H.degree w ≤ D) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 5)
    (hbudget : (r : ℝ) * (5 * ε) ≤ 1 / 2) (c : SeedDescription F H S)
    (hacc : IncidenceSeedAccurate F H J f right high d S p ε c)
    (hgood : copyRawEdges f ∉ starImagePatterns H J (copyVertices f) r F.edgeSet.ncard D P
      ((F.edgeSet.ncard : ℝ) / 128 * Real.log ((P : ℝ) / T))) :
    (d : ℝ) * (smallCommonNeighborhoodRoles J
      (incidenceCandidateList F H J right high d S p (1 - 4 * ε) c) r T).card <
        (F.edgeSet.ncard : ℝ) / 8 := by
  have hlog : 0 < Real.log ((P : ℝ) / T) := Real.log_pos ((one_lt_div hT).mpr hTP)
  have h := incidence_small_common_roles_weighted_bound F H J hJ f right high d S r D P
    hn hd hP T p ε ((F.edgeSet.ncard : ℝ) / 128 * Real.log ((P : ℝ) / T))
    hp hT hTP.le hD hε₀ hε₁ hbudget c hacc hgood
  have h' : (d : ℝ) * (smallCommonNeighborhoodRoles J
      (incidenceCandidateList F H J right high d S p (1 - 4 * ε) c) r T).card *
        Real.log ((P : ℝ) / T) < (F.edgeSet.ncard : ℝ) / 8 * Real.log ((P : ℝ) / T) := by
    nlinarith only [h]
  exact (mul_lt_mul_iff_of_pos_right hlog).mp h'

end Erdos911
