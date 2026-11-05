import Erdos911.PaddedCandidateTuples

namespace Erdos911

noncomputable def smallCommonNeighborhoodRoles {V W : Type*} [Fintype V]
    [Fintype W] [DecidableEq W] (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ U : Finset W,
    U ⊆ L v ∧ U.Nonempty ∧ U.card ≤ s ∧ ((commonCenters J.Adj U).card : ℝ) ≤ T)

theorem mem_smallCommonNeighborhoodRoles {V W : Type*} [Fintype V]
    [Fintype W] [DecidableEq W] (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ) (v : V) :
    v ∈ smallCommonNeighborhoodRoles J L s T ↔ ∃ U : Finset W,
      U ⊆ L v ∧ U.Nonempty ∧ U.card ≤ s ∧ ((commonCenters J.Adj U).card : ℝ) ≤ T := by
  classical
  simp only [smallCommonNeighborhoodRoles, Finset.mem_filter, Finset.mem_univ, true_and]

/-- All small-common-neighborhood witnesses can be chosen simultaneously
and encoded in the tuple representation used by star-deficit pruning. -/
theorem exists_small_common_role_tuples {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj]
    (L : V → Finset W) (s : ℕ) (T : ℝ) :
    ∃ q : V → Fin s → Option W,
      (∀ v i x, q v i = some x → x ∈ L v) ∧
      (∀ v, v ∈ smallCommonNeighborhoodRoles J L s T →
        ¬inactiveStarTuple (q v) ∧ ((tupleCommonNeighbors J (q v)).card : ℝ) ≤ T) ∧
      (∀ v, v ∉ smallCommonNeighborhoodRoles J L s T → inactiveStarTuple (q v)) := by
  classical
  let bad := smallCommonNeighborhoodRoles J L s T
  have hex (v : V) (hv : v ∈ bad) : ∃ U : Finset W,
      U ⊆ L v ∧ U.Nonempty ∧ U.card ≤ s ∧ ((commonCenters J.Adj U).card : ℝ) ≤ T :=
    (mem_smallCommonNeighborhoodRoles J L s T v).mp hv
  let U (v : V) := if hv : v ∈ bad then (hex v hv).choose else ∅
  have hspec (v : V) (hv : v ∈ bad) :
      U v ⊆ L v ∧ (U v).Nonempty ∧ (U v).card ≤ s ∧ ((commonCenters J.Adj (U v)).card : ℝ) ≤ T := by
    dsimp only [U]
    rw [dite_eq_left hv]
    exact (hex v hv).choose_spec
  have hempty (v : V) (hv : v ∉ bad) : U v = ∅ := by
    dsimp only [U]
    rw [dite_eq_right hv]
  let q := fun v => paddedCandidateTuple (U v) s
  refine ⟨q, ?_, ?_, ?_⟩
  · intro v i x hq
    have hx := paddedCandidateTuple_mem (U v) s i x hq
    by_cases hv : v ∈ bad
    · exact (hspec v hv).1 hx
    · rw [hempty v hv] at hx
      exact (Finset.notMem_empty x hx).elim
  · intro v hv
    obtain ⟨_, hnonempty, hsize, hcommon⟩ := hspec v hv
    refine ⟨paddedCandidateTuple_active (U v) s hsize hnonempty, ?_⟩
    change ((tupleCommonNeighbors J (paddedCandidateTuple (U v) s)).card : ℝ) ≤ T
    rw [tupleCommonNeighbors_paddedCandidateTuple J (U v) s hsize]
    exact hcommon
  · intro v hv i
    change paddedCandidateTuple (U v) s i = none
    rw [hempty v hv]
    simp [paddedCandidateTuple]

/-- A copy surviving star-deficit deletion cannot have large total degree
on roles whose dense candidate lists contain a small common neighborhood. -/
theorem small_common_roles_weighted_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (f : G.Copy H) (L : V → Finset W) (s P : ℕ) (T ε ℓ : ℝ)
    (hP : 0 < P) (hT : 0 < T) (hTP : T ≤ P)
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hdegree : ∀ v, 0 < G.degree v)
    (hdense : ∀ v w, w ∈ L v → (1 - ε) * G.degree v ≤
      ((slotGoodNeighbors G J f v (some w)).card : ℝ))
    (hgood : ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P ℓ) :
    (∑ v ∈ smallCommonNeighborhoodRoles J L s T, (G.degree v : ℝ)) * Real.log ((P : ℝ) / T) < 4 * ℓ := by
  classical
  obtain ⟨q, hsource, hbad, hinactive⟩ := exists_small_common_role_tuples J L s T
  let bad := smallCommonNeighborhoodRoles J L s T
  have hlarge : ∀ v i, (1 - ε) * G.degree v ≤ (slotGoodNeighbors G J f v (q v i)).card := by
    intro v i
    cases hqi : q v i with
    | none =>
      have heq : slotGoodNeighbors G J f v none = G.neighborFinset v := by
        ext u
        simp only [mem_slotGoodNeighbors, reduceCtorEq, false_implies, implies_true, and_true,
          SimpleGraph.mem_neighborFinset]
      rw [heq, G.card_neighborFinset_eq_degree]
      nlinarith only [mul_nonneg hε₀ (Nat.cast_nonneg (α := ℝ) (G.degree v))]
    | some w => exact hdense v w (hsource v i w hqi)
  have hhalf (v : V) : (G.degree v : ℝ) ≤ 2 * (tupleGoodNeighbors G J f v (q v)).card :=
    tupleGoodNeighbors_half_card G J f v (q v) ε hbudget (hlarge v)
  have hcapPos (v : V) : 0 < starWitnessCapacity J P (q v) :=
    tupleWitnessCapacity_pos G J f v (q v) P hP (hdegree v) (hhalf v)
  have hupper : ∀ v, ¬inactiveStarTuple (q v) → (tupleCommonNeighbors J (q v)).card ≤ P := by
    intro v hv
    have hvbad : v ∈ bad := by
      by_contra hn
      exact hv (hinactive v hn)
    exact_mod_cast (hbad v hvbad).2.trans hTP
  have hcapLe (v : V) : starWitnessCapacity J P (q v) ≤ P := by
    unfold starWitnessCapacity
    split_ifs with hv
    · exact le_rfl
    · exact hupper v hv
  have hlogNonneg (v : V) : 0 ≤ Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    apply Real.log_nonneg
    apply (one_le_div (by exact_mod_cast hcapPos v : (0 : ℝ) < starWitnessCapacity J P (q v))).mpr
    exact_mod_cast hcapLe v
  have hmargin (v : V) (hv : v ∈ bad) : Real.log ((P : ℝ) / T) ≤
      Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    have hcapT : (starWitnessCapacity J P (q v) : ℝ) ≤ T := by
      unfold starWitnessCapacity
      rw [ite_eq_right (hbad v hv).1]
      exact (hbad v hv).2
    apply Real.log_le_log (div_pos (by exact_mod_cast hP) hT)
    apply (div_le_div_iff₀ hT (by exact_mod_cast hcapPos v)).mpr
    exact mul_le_mul_of_nonneg_left hcapT (Nat.cast_nonneg (α := ℝ) P)
  have htotal : (∑ v ∈ bad, (G.degree v : ℝ)) * Real.log ((P : ℝ) / T) ≤
      ∑ v, (G.degree v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    rw [Finset.sum_mul]
    apply (Finset.sum_le_sum (fun v hv =>
      mul_le_mul_of_nonneg_left (hmargin v hv) (Nat.cast_nonneg (α := ℝ) (G.degree v)))).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => mul_nonneg (Nat.cast_nonneg _) (hlogNonneg v))
  have hstrict : (∑ v, (G.degree v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v))) < 4 * ℓ := by
    by_contra hn
    exact hgood (copy_star_deficit_of_dense_tuples G H J hJ f s P ℓ ε q
      hP hε₁ hbudget hdegree hlarge hupper (le_of_not_gt hn))
  exact htotal.trans_lt hstrict

theorem small_common_roles_degree_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (f : G.Copy H) (L : V → Finset W) (s P : ℕ) (T ε : ℝ)
    (hP : 0 < P) (hT : 0 < T) (hTP : T < P)
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hdegree : ∀ v, 0 < G.degree v)
    (hdense : ∀ v w, w ∈ L v → (1 - ε) * G.degree v ≤
      ((slotGoodNeighbors G J f v (some w)).card : ℝ))
    (hgood : ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P
      ((G.edgeSet.ncard : ℝ) / 32 * Real.log ((P : ℝ) / T))) :
    (∑ v ∈ smallCommonNeighborhoodRoles J L s T, (G.degree v : ℝ)) < (G.edgeSet.ncard : ℝ) / 8 := by
  have hlog : 0 < Real.log ((P : ℝ) / T) :=
    Real.log_pos ((one_lt_div hT).mpr hTP)
  have h := small_common_roles_weighted_bound G H J hJ f L s P T ε
    ((G.edgeSet.ncard : ℝ) / 32 * Real.log ((P : ℝ) / T))
    hP hT hTP.le hε₀ hε₁ hbudget hdegree hdense hgood
  have hstrict : (∑ v ∈ smallCommonNeighborhoodRoles J L s T, (G.degree v : ℝ)) *
      Real.log ((P : ℝ) / T) < ((G.edgeSet.ncard : ℝ) / 8) * Real.log ((P : ℝ) / T) := by
    nlinarith only [h]
  exact (mul_lt_mul_iff_of_pos_right hlog).mp hstrict

end Erdos911
