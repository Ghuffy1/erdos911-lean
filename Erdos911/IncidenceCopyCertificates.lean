import Erdos911.IncidenceRetention
import Erdos911.ThickCandidateLists

namespace Erdos911

/-- An actual copy supplies a connected seed, uniformly small candidate
lists, and an explicit exception budget depending only on deleted edges. -/
theorem exists_incidence_copy_lists {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J K : SimpleGraph W)
    [DecidableRel J.Adj] [DecidableRel K.Adj]
    (hF : F.Connected) (f : F.Copy H) (right : Finset (Fin n))
    (d D s q T : ℕ) (hd : 0 < d) (hdD : d ≤ D)
    (hmin : ∀ v, d ≤ F.degree v) (hright : ∀ v ∈ right, F.degree v ≤ d)
    (hhost : ∀ w, J.degree w ≤ D) (hH : H ≤ lowEndpointPrunedGraph K T)
    (hq : 0 < q) (hsmall : 8 * q ≤ d)
    (p ε ρ : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hε₀ : 0 < ε) (hε₁ : ε < 1 / 5)
    (hρ : 0 ≤ ρ) (hgap : ρ * d + 4 * q < (1 - 5 * ε) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hseed : 3 * n * (p + Real.exp (-(p * d)) + 2 * Real.exp (-(p * d) / 2048) +
      (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512)) ≤ s) :
    ∃ (c : SeedDescription F H s) (E : Finset (Fin n)),
      seedMapAgrees F H s c f ∧
      (E.card : ℝ) ≤ 4 * (F \ copyRetainedGraph J f).edgeFinset.card / (ε * d) ∧
      (∀ v, (incidenceCandidateList F H J right (highHostVertices K T)
        d s p (1 - 4 * ε) c v).card < q) ∧
      (∀ v w, w ∈ incidenceCandidateList F H J right (highHostVertices K T)
        d s p (1 - 4 * ε) c v →
        (1 - 5 * ε) * (copyHighNeighbors F f (highHostVertices K T) v).card ≤
          ((candidateSlice (copyHighNeighbors F f (highHostVertices K T) v)
            (fun j => J.neighborFinset (f j)) w).card : ℝ)) ∧
      (∀ v, (incidenceCandidateList F H J right (highHostVertices K T)
          d s p (1 - 4 * ε) c v).Nonempty → v ∉ E →
        f v ∈ incidenceCandidateList F H J right (highHostVertices K T)
          d s p (1 - 4 * ε) c v) ∧
      ∀ v, (incidenceCandidateList F H J right (highHostVertices K T)
          d s p (1 - 4 * ε) c v).Nonempty → ∃ u, F.Adj v u ∧ f u ∈ highHostVertices K T := by
  obtain ⟨c, hagree, hacc⟩ := exists_adaptive_incidence_seed F H J hF f right (highHostVertices K T)
    d D s hd hdD hmin hright hhost p ε hp₀ hp₁ hε₀.le (by linarith) hseed
  let E := incidenceRetentionDefects F H J f right (highHostVertices K T) d ε
  have hτ : 0 < 1 - 4 * ε := by linarith
  refine ⟨c, E, hagree, ?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos hε₀ (by exact_mod_cast hd))).mpr
    simpa only [E, mul_assoc, mul_comm, mul_left_comm] using
      incidenceRetentionDefects_card_bound F H J f right (highHostVertices K T) d ε
  · exact incidenceCandidateList_card_lt F H J f right (highHostVertices K T) d s q hd hq hsmall
      p ε ρ hp₀ hρ hgap hnodense c hacc
  · exact incidence_candidate_fraction_lower F H J f right (highHostVertices K T) d s hd p ε hp₀ c hacc
  · exact incidence_true_image_outside_defects F H J K T hH f right d s hd p ε hp₀ hε₀.le hτ c hagree hacc
  · intro v hne
    obtain ⟨w, hw⟩ := hne
    exact incidence_candidate_actual_high_neighbor F H J right (highHostVertices K T)
      d s p (1 - 4 * ε) hτ c f hagree v w hw

/-- The matching is chosen from the lists. Exceptions are counted only
on roles with nonempty lists, so unused left roles do not consume the budget. -/
theorem incidence_matching_card_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (L : V → Finset W) (r : ℕ) (T : ℝ)
    (right A E : Finset V) (f : V → W) (hf : Function.Injective f)
    (hnonempty : ∀ v ∈ right, v ∉ A → v ∉ E → (L v).Nonempty)
    (htrue : ∀ v, (L v).Nonempty → v ∉ E → f v ∈ L v) :
    right.card ≤ (matchedRoles
      (maximumListMatching (fun v : thickCandidateRoles J L r T => L v.val))).card +
        (smallCommonNeighborhoodRoles J L r T).card + A.card + 2 * E.card := by
  classical
  let good := thickCandidateRoles J L r T
  let bad := smallCommonNeighborhoodRoles J L r T
  let lists := fun v : good => L v.val
  let exceptions := (Finset.univ : Finset good).filter (fun v => v.val ∈ E)
  have hsub : right ⊆ ((good ∪ bad) ∪ A) ∪ E := by
    intro v hv
    by_cases hvA : v ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvA)
    by_cases hvE : v ∈ E
    · exact Finset.mem_union_right _ hvE
    by_cases hvBad : v ∈ bad
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hvBad))
    have hvGood : v ∈ good := (mem_thickCandidateRoles J L r T v).mpr
      ⟨hnonempty v hv hvA hvE, hvBad⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hvGood))
  have hcover : right.card ≤ good.card + bad.card + A.card + E.card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
  have hExsub : exceptions.image Subtype.val ⊆ E := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hw).2
  have hE : exceptions.card ≤ E.card := by
    rw [← Finset.card_image_of_injective exceptions Subtype.val_injective]
    exact Finset.card_le_card hExsub
  have hmatching := maximum_list_matching_size lists (fun v : good => f v.val)
    (hf.comp Subtype.val_injective) exceptions (by
      intro v hv
      apply htrue v.val ((mem_thickCandidateRoles J L r T v.val).mp v.property).1
      intro hvE
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvE⟩))
  have hsize : good.card ≤ (matchedRoles (maximumListMatching lists)).card + E.card := by
    simpa only [Fintype.card_coe] using hmatching.trans (Nat.add_le_add_left hE _)
  change right.card ≤ (matchedRoles (maximumListMatching lists)).card + bad.card + A.card + 2 * E.card
  omega

end Erdos911
