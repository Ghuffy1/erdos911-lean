import Erdos911.SubsetTupleWitnesses
import Erdos911.SmallCommonRoleBounds

namespace Erdos911

theorem smallCommonNeighborhoodRoles_list_nonempty {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (L : V → Finset W) (s : ℕ) (T : ℝ) (v : V)
    (hv : v ∈ smallCommonNeighborhoodRoles J L s T) : (L v).Nonempty := by
  obtain ⟨U, hUL, hU, _, _⟩ := (mem_smallCommonNeighborhoodRoles J L s T v).mp hv
  exact hU.mono hUL

/-- A large collection of small-common-neighborhood roles forces an
image pattern with a prescribed logarithmic deficit. Only the subsets
`N v`, rather than the full neighborhoods, enter the density assumptions. -/
theorem subset_small_common_roles_pattern {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (f : F.Copy H)
    (L : V → Finset W) (N : V → Finset V) (d s D P : ℕ) (T ε ℓ : ℝ)
    (hd : 0 < d) (hP : 0 < P) (hT : 0 < T) (hTP : T ≤ P)
    (hD : ∀ w, H.degree w ≤ D) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hN : ∀ v, N v ⊆ F.neighborFinset v)
    (hlarge : ∀ v, (L v).Nonempty → d ≤ 4 * (N v).card)
    (hdense : ∀ v w, w ∈ L v → (1 - ε) * (N v).card ≤
      (subsetSlotNeighbors (N v) J f (some w)).card)
    (hmass : 16 * ℓ ≤ (d : ℝ) * (smallCommonNeighborhoodRoles J L s T).card *
      Real.log ((P : ℝ) / T)) :
    copyRawEdges f ∈ starImagePatterns H J (copyVertices f) s F.edgeSet.ncard D P ℓ := by
  classical
  obtain ⟨q, hsource, hbad, hinactive⟩ := exists_small_common_role_tuples J L s T
  let bad := smallCommonNeighborhoodRoles J L s T
  have hslot (v : V) (i : Fin s) : (1 - ε) * (N v).card ≤
      (subsetSlotNeighbors (N v) J f (q v i)).card := by
    cases hqi : q v i with
    | none =>
      have heq : subsetSlotNeighbors (N v) J f none = N v := by
        ext u
        simp only [mem_subsetSlotNeighbors, reduceCtorEq, false_implies, implies_true, and_true]
      rw [heq]
      have hnonneg := mul_nonneg hε₀ (Nat.cast_nonneg (α := ℝ) (N v).card)
      linarith
    | some w => exact hdense v w (hsource v i w hqi)
  have hNpos (v : V) (hv : v ∈ bad) : (N v).Nonempty := by
    have h := hlarge v (smallCommonNeighborhoodRoles_list_nonempty J L s T v hv)
    exact Finset.card_pos.mp (by omega)
  have hnear (v : V) : q v ∈ starWitnessTuples H (f v) s := by
    by_cases hv : v ∈ bad
    · exact subset_starWitnessTuples_of_dense_slots F H J hJ f v (N v) (hN v) (hNpos v hv)
        s (q v) ε hε₁ (hslot v)
    · apply Fintype.mem_piFinset.mpr
      intro i
      rw [hinactive v hv i, optionalTwoStepNeighbors]
      exact Finset.mem_insert_self _ _
  have hcapacity (v : V) : 0 < starWitnessCapacity J P (q v) ∧ starWitnessCapacity J P (q v) ≤ P := by
    by_cases hv : v ∈ bad
    · refine ⟨subset_tuple_star_capacity_pos F J f v (N v) (hN v) (hNpos v hv) s P hP
        (q v) ε hbudget (hslot v), ?_⟩
      have hcapT : (starWitnessCapacity J P (q v) : ℝ) ≤ T := by
        simp only [starWitnessCapacity, ite_eq_right (hbad v hv).1]
        exact (hbad v hv).2
      exact_mod_cast hcapT.trans hTP
    · simpa only [starWitnessCapacity, ite_eq_left (hinactive v hv)] using
        (show 0 < P ∧ P ≤ P from ⟨hP, le_rfl⟩)
  have hlog (v : V) : 0 ≤ Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    apply Real.log_nonneg
    apply (one_le_div (by exact_mod_cast (hcapacity v).1 : (0 : ℝ) < starWitnessCapacity J P (q v))).mpr
    exact_mod_cast (hcapacity v).2
  have hlogT : 0 ≤ Real.log ((P : ℝ) / T) :=
    Real.log_nonneg ((one_le_div hT).mpr hTP)
  have hmargin (v : V) (hv : v ∈ bad) : Real.log ((P : ℝ) / T) ≤
      Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    have hcapT : (starWitnessCapacity J P (q v) : ℝ) ≤ T := by
      simp only [starWitnessCapacity, ite_eq_right (hbad v hv).1]
      exact (hbad v hv).2
    apply Real.log_le_log (div_pos (by exact_mod_cast hP) hT)
    apply (div_le_div_iff₀ hT (by exact_mod_cast (hcapacity v).1)).mpr
    exact mul_le_mul_of_nonneg_left hcapT (Nat.cast_nonneg (α := ℝ) P)
  have hrestricted (v : V) (hv : v ∈ bad) : (d : ℝ) / 8 ≤
      (copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card := by
    have hlargeR : (d : ℝ) ≤ 4 * (N v).card := by
      exact_mod_cast hlarge v (smallCommonNeighborhoodRoles_list_nonempty J L s T v hv)
    have h := subset_tuple_star_edge_mass F H J f v (N v) (hN v) d s hlargeR
      (q v) (hbad v hv).1 ε hbudget (hslot v)
    linarith only [h]
  have hweighted : (d : ℝ) / 8 * bad.card * Real.log ((P : ℝ) / T) ≤
      ∑ v, ((copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    calc
      _ = ∑ _v ∈ bad, (d : ℝ) / 8 * Real.log ((P : ℝ) / T) := by simp; ring
      _ ≤ ∑ v ∈ bad, ((copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card : ℝ) *
          Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) :=
        Finset.sum_le_sum (fun v hv => mul_le_mul (hrestricted v hv) (hmargin v hv)
          hlogT (Nat.cast_nonneg _))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun v _ _ => mul_nonneg (Nat.cast_nonneg _) (hlog v))
  apply copy_starPattern_of_intersection_deficit F H J f s D P ℓ q hD hnear hcapacity
  change 16 * ℓ ≤ (d : ℝ) * bad.card * Real.log ((P : ℝ) / T) at hmass
  nlinarith only [hmass, hweighted]

theorem subset_small_common_roles_weighted_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (f : F.Copy H)
    (L : V → Finset W) (N : V → Finset V) (d s D P : ℕ) (T ε ℓ : ℝ)
    (hd : 0 < d) (hP : 0 < P) (hT : 0 < T) (hTP : T ≤ P)
    (hD : ∀ w, H.degree w ≤ D) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1)
    (hbudget : (s : ℝ) * ε ≤ 1 / 2) (hN : ∀ v, N v ⊆ F.neighborFinset v)
    (hlarge : ∀ v, (L v).Nonempty → d ≤ 4 * (N v).card)
    (hdense : ∀ v w, w ∈ L v → (1 - ε) * (N v).card ≤
      (subsetSlotNeighbors (N v) J f (some w)).card)
    (hgood : copyRawEdges f ∉ starImagePatterns H J (copyVertices f) s F.edgeSet.ncard D P ℓ) :
    (d : ℝ) * (smallCommonNeighborhoodRoles J L s T).card * Real.log ((P : ℝ) / T) < 16 * ℓ := by
  apply lt_of_not_ge
  intro h
  exact hgood (subset_small_common_roles_pattern F H J hJ f L N d s D P T ε ℓ hd hP hT hTP
    hD hε₀ hε₁ hbudget hN hlarge hdense h)

end Erdos911
