import Erdos911.SmallCommonRoleBounds
import Erdos911.ListMatching

namespace Erdos911

theorem commonCenters_antitone {X W : Type*} [Fintype W]
    (R : X → W → Prop) (U V : Finset X) (hUV : U ⊆ V) : commonCenters R V ⊆ commonCenters R U := by
  intro z hz
  exact (mem_commonCenters_iff R U z).mpr (fun x hx =>
    (mem_commonCenters_iff R V z).mp hz x (hUV hx))

theorem common_neighborhood_of_good_role {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ)
    (hs : 1 ≤ s) (v : V) (hnonempty : (L v).Nonempty)
    (hgood : v ∉ smallCommonNeighborhoodRoles J L s T) :
    ∀ U ⊆ L v, U.card ≤ s → T ≤ ((commonCenters J.Adj U).card : ℝ) := by
  classical
  have hstrict : ∀ U ⊆ L v, U.Nonempty → U.card ≤ s → T < ((commonCenters J.Adj U).card : ℝ) := by
    intro U hU hUnonempty hsize
    by_contra hn
    exact hgood ((mem_smallCommonNeighborhoodRoles J L s T v).mpr
      ⟨U, hU, hUnonempty, hsize, le_of_not_gt hn⟩)
  intro U hU hsize
  by_cases hUnonempty : U.Nonempty
  · exact (hstrict U hU hUnonempty hsize).le
  · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUnonempty
    obtain ⟨x, hx⟩ := hnonempty
    have hsingle := hstrict {x} (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)
      (by simpa only [Finset.card_singleton] using hs)
    have hmono : ((commonCenters J.Adj {x}).card : ℝ) ≤ (commonCenters J.Adj U).card := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      apply commonCenters_antitone
      rw [hUempty]
      exact Finset.empty_subset _
    exact hsingle.le.trans hmono

noncomputable def thickCandidateRoles {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (L v).Nonempty ∧ v ∉ smallCommonNeighborhoodRoles J L s T)

theorem mem_thickCandidateRoles {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ) (v : V) :
    v ∈ thickCandidateRoles J L s T ↔ (L v).Nonempty ∧ v ∉ smallCommonNeighborhoodRoles J L s T := by
  classical
  simp only [thickCandidateRoles, Finset.mem_filter, Finset.mem_univ, true_and]

theorem thickCandidateRoles_common {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ)
    (hs : 1 ≤ s) (v : thickCandidateRoles J L s T) :
    ∀ U ⊆ L v.val, U.card ≤ s → T ≤ ((commonCenters J.Adj U).card : ℝ) := by
  obtain ⟨hne, hgood⟩ := (mem_thickCandidateRoles J L s T v.val).mp v.property
  exact common_neighborhood_of_good_role J L s T hs v.val hne hgood

/-- Missing candidate lists are charged to the exceptional set, while
the remaining rejected lists are charged by their total target degree. -/
theorem thick_candidate_degree_cover {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : SimpleGraph W)
    (L : V → Finset W) (s Δ : ℕ) (T : ℝ) (f : V → W) (S : Finset V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (htrue : ∀ v, v ∉ S → f v ∈ L v) :
    2 * G.edgeFinset.card ≤ Δ * (thickCandidateRoles J L s T).card +
      (∑ v ∈ smallCommonNeighborhoodRoles J L s T, G.degree v) + Δ * S.card := by
  classical
  let good := thickCandidateRoles J L s T
  let bad := smallCommonNeighborhoodRoles J L s T
  have hpoint (v : V) : G.degree v ≤
      (if v ∈ good then Δ else 0) + (if v ∈ bad then G.degree v else 0) +
        (if v ∈ S then Δ else 0) := by
    by_cases hv : v ∈ good
    · simp only [ite_eq_left hv]
      split_ifs <;> have h := hΔ v <;> omega
    by_cases hb : v ∈ bad
    · simp only [ite_eq_right hv, ite_eq_left hb, zero_add]
      split_ifs <;> omega
    have hvS : v ∈ S := by
      by_contra hn
      exact hv ((mem_thickCandidateRoles J L s T v).mpr ⟨⟨f v, htrue v hn⟩, hb⟩)
    simpa only [ite_eq_right hv, ite_eq_right hb, ite_eq_left hvS, zero_add] using hΔ v
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hpoint v)
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  simpa only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.mul_comm, Nat.cast_id, good, bad] using hsum

/-- The maximum matching depends on the candidate lists alone. A valid
copy outside an exceptional set certifies its retained edge-scale mass. -/
theorem thick_matching_degree_cover {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : SimpleGraph W)
    (L : V → Finset W) (s Δ : ℕ) (T : ℝ) (f : V → W) (hf : Function.Injective f) (S : Finset V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (htrue : ∀ v, v ∉ S → f v ∈ L v) :
    2 * G.edgeFinset.card ≤ Δ * (matchedRoles
      (maximumListMatching (fun v : thickCandidateRoles J L s T => L v.val))).card +
      (∑ v ∈ smallCommonNeighborhoodRoles J L s T, G.degree v) + 2 * Δ * S.card := by
  classical
  let good := thickCandidateRoles J L s T
  let lists := fun v : good => L v.val
  let exceptional := (Finset.univ : Finset good).filter (fun v => v.val ∈ S)
  have hexceptional : exceptional.card ≤ S.card := by
    have hsub : exceptional.image Subtype.val ⊆ S := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    calc
      exceptional.card = (exceptional.image Subtype.val).card :=
        (Finset.card_image_of_injective exceptional Subtype.val_injective).symm
      _ ≤ S.card := Finset.card_le_card hsub
  have hmatching := maximum_list_matching_size lists (fun v : good => f v.val)
    (hf.comp Subtype.val_injective) exceptional (by
      intro v hv
      apply htrue v.val
      intro hvs
      exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvs⟩))
  have hsize : good.card ≤ (matchedRoles (maximumListMatching lists)).card + S.card := by
    simpa only [Fintype.card_coe] using hmatching.trans (Nat.add_le_add_left hexceptional _)
  have hscaled := Nat.mul_le_mul_left Δ hsize
  have hcover := thick_candidate_degree_cover G J L s Δ T f S hΔ htrue
  change 2 * G.edgeFinset.card ≤ Δ * (matchedRoles (maximumListMatching lists)).card +
    (∑ v ∈ smallCommonNeighborhoodRoles J L s T, G.degree v) + 2 * Δ * S.card
  change 2 * G.edgeFinset.card ≤ Δ * good.card +
    (∑ v ∈ smallCommonNeighborhoodRoles J L s T, G.degree v) + Δ * S.card at hcover
  nlinarith only [hscaled, hcover]

end Erdos911
