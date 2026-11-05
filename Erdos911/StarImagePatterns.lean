import Erdos911.StarNeighborhoods
import Erdos911.RestrictedStarAssignment
import Erdos911.InducedHostEdges

namespace Erdos911

noncomputable def starImagePatterns {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (s a D P : ℕ) (L : ℝ) : Finset (Finset (Sym2 W)) := by
  classical
  exact (validStarWitnesses H J U s P).biUnion (fun q =>
    restrictedStarDescriptions (inducedHostEdges H U)
      (fun v : U => starWitnessEdges J v.val (q v))
      (fun v : U => starWitnessCapacity J P (q v)) a D P L)

theorem mem_starImagePatterns {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (s a D P : ℕ) (L : ℝ) (E : Finset (Sym2 W)) :
    E ∈ starImagePatterns H J U s a D P L ↔
      ∃ q ∈ validStarWitnesses H J U s P,
        E ∈ restrictedStarDescriptions (inducedHostEdges H U)
          (fun v : U => starWitnessEdges J v.val (q v))
          (fun v : U => starWitnessCapacity J P (q v)) a D P L := by
  classical
  exact Finset.mem_biUnion

theorem starImagePatterns_card_bound {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (s a D P : ℕ) (L : ℝ) (hU : U.Nonempty) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D) (hlocal : (inducedHostEdges H U).card ≤ P * U.card) :
    ((starImagePatterns H J U s a D P L).card : ℝ) ≤
      (((D ^ 2 + 1) ^ (s * U.card) : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) ^ U.card *
        Real.exp ((a : ℝ) * Real.log ((P * U.card : ℝ) / a) - L + 2 * a) := by
  classical
  have hk : 0 < Fintype.card U := by simpa only [Fintype.card_coe] using hU.card_pos
  have hcapacities : ∀ q ∈ validStarWitnesses H J U s P, ∀ v : U,
      0 < starWitnessCapacity J P (q v) := by
    intro q hq v
    exact ((mem_validStarWitnesses H J U s P q).mp hq).2 v |>.1
  have hcount := witness_restrictedStarDescriptions_card_bound
    (validStarWitnesses H J U s P) (inducedHostEdges H U)
    (fun q v => starWitnessEdges J v.val (q v))
    (fun q v => starWitnessCapacity J P (q v)) a D P L hP hcapacities hk ha
    (by simpa only [Fintype.card_coe] using hlocal)
    (fun q _ v => starWitnessEdges_card_le J P v.val (q v))
  have hcount' : ((starImagePatterns H J U s a D P L).card : ℝ) ≤
      (validStarWitnesses H J U s P).card * ((D + 1 : ℕ) : ℝ) ^ U.card *
        Real.exp ((a : ℝ) * Real.log ((P * U.card : ℝ) / a) - L + 2 * a) := by
    simpa only [starImagePatterns, Fintype.card_coe] using hcount
  have hwitness : ((validStarWitnesses H J U s P).card : ℝ) ≤
      (((D ^ 2 + 1) ^ (s * U.card) : ℕ) : ℝ) := by
    exact_mod_cast validStarWitnesses_card_le H J D hD U s P
  exact hcount'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hwitness (by positivity)) (Real.exp_pos _).le)

/-- A large deficit witnessed by nearby tuples and their actual common
neighborhoods. Its definition uses only the host vertex and edge images. -/
noncomputable def IsStarDeficitImage {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (E : Finset (Sym2 W)) (s P : ℕ) (L : ℝ) : Prop :=
  ∃ q ∈ validStarWitnesses H J U s P,
    (∀ v : U, (edgeRoleDegree E v.val : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) ≤
      2 * (E ∩ starWitnessEdges J v.val (q v)).card * Real.log ((P : ℝ) / starWitnessCapacity J P (q v))) ∧
    4 * L ≤ ∑ v : U, (edgeRoleDegree E v.val : ℝ) *
      Real.log ((P : ℝ) / starWitnessCapacity J P (q v))

theorem starDeficitImage_mem_patterns {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (E : Finset (Sym2 W)) (s a D P : ℕ) (L : ℝ)
    (hU : U.Nonempty) (hE : E ⊆ inducedHostEdges H U) (hcard : E.card = a)
    (hD : ∀ w, H.degree w ≤ D) (hbad : IsStarDeficitImage H J U E s P L) :
    E ∈ starImagePatterns H J U s a D P L := by
  classical
  let : Nonempty U := let ⟨u, hu⟩ := hU; ⟨⟨u, hu⟩⟩
  obtain ⟨q, hq, hcoverage, hdeficit⟩ := hbad
  let A := fun v : U => starWitnessEdges J v.val (q v)
  let R := fun v : U => E ∩ A v
  have hC := ((mem_validStarWitnesses H J U s P q).mp hq).2
  have hincident : ∀ v : U, ∀ e ∈ R v, v.val ∈ e := by
    intro v e he
    exact starWitnessEdges_incident J v.val (q v) e (Finset.mem_inter.mp he).2
  have hRcard : ∀ v : U, (R v).card ≤ D := by
    intro v
    apply (incident_subset_card_le_degree H (R v) v.val ?_ (hincident v)).trans (hD v.val)
    exact Finset.inter_subset_left.trans (hE.trans (Finset.filter_subset _ _))
  have hpattern := finite_edges_mem_restrictedStarDescriptions (fun v : U => v.val)
    Subtype.val_injective E (inducedHostEdges H U) (fun v => edgeRoleDegree E v.val)
    A R (fun v => starWitnessCapacity J P (q v)) D P L hC hE
    (fun _ => Finset.inter_subset_left) (fun _ => Finset.inter_subset_right)
    hincident hRcard hcoverage hdeficit
  rw [hcard] at hpattern
  exact (mem_starImagePatterns H J U s a D P L E).mpr ⟨q, hq, hpattern⟩

end Erdos911
