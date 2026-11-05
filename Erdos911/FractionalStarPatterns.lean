import Erdos911.CopyStarWitnesses

namespace Erdos911

/-- Restricted edge mass, rather than half of every vertex degree, is
enough for the finite star-pattern count. This allows incidence roles
with only a quarter-sized high-neighbor subset. -/
theorem starPattern_mem_of_intersection_deficit {W : Type*}
    [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (E : Finset (Sym2 W)) (s a D P : ℕ) (L : ℝ)
    (hU : U.Nonempty) (hE : E ⊆ inducedHostEdges H U) (hcard : E.card = a)
    (hD : ∀ w, H.degree w ≤ D) (q : U → Fin s → Option W)
    (hq : q ∈ validStarWitnesses H J U s P)
    (hdeficit : 2 * L ≤ ∑ v : U,
      ((E ∩ starWitnessEdges J v.val (q v)).card : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q v))) :
    E ∈ starImagePatterns H J U s a D P L := by
  classical
  let : Nonempty U := let ⟨u, hu⟩ := hU; ⟨⟨u, hu⟩⟩
  let A := fun v : U => starWitnessEdges J v.val (q v)
  let R := fun v : U => E ∩ A v
  let m := fun v : U => 2 * (R v).card
  have hC := ((mem_validStarWitnesses H J U s P q).mp hq).2
  have hincident : ∀ v : U, ∀ e ∈ R v, v.val ∈ e := by
    intro v e he
    exact starWitnessEdges_incident J v.val (q v) e (Finset.mem_inter.mp he).2
  have hRcard : ∀ v : U, (R v).card ≤ D := by
    intro v
    apply (incident_subset_card_le_degree H (R v) v.val ?_ (hincident v)).trans (hD v.val)
    exact Finset.inter_subset_left.trans (hE.trans (Finset.filter_subset _ _))
  have hcoverage (v : U) : (m v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) ≤
      2 * (R v).card * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    simp only [m, Nat.cast_mul, Nat.cast_ofNat, le_refl]
  have hmass : 4 * L ≤ ∑ v : U, (m v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    have hsum : (∑ v : U, (m v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v))) =
        2 * ∑ v : U, ((R v).card : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
      simp only [m, Nat.cast_mul, Nat.cast_ofNat, Finset.mul_sum, mul_assoc]
    rw [hsum]
    change 4 * L ≤ 2 * ∑ v : U,
      ((E ∩ starWitnessEdges J v.val (q v)).card : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q v))
    linarith only [hdeficit]
  have hpattern := finite_edges_mem_restrictedStarDescriptions (fun v : U => v.val)
    Subtype.val_injective E (inducedHostEdges H U) m A R
    (fun v => starWitnessCapacity J P (q v)) D P L hC hE
    (fun _ => Finset.inter_subset_left) (fun _ => Finset.inter_subset_right)
    hincident hRcard hcoverage hmass
  rw [hcard] at hpattern
  exact (mem_starImagePatterns H J U s a D P L E).mpr ⟨q, hq, hpattern⟩

theorem copy_starPattern_of_intersection_deficit {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : G.Copy H) (s D P : ℕ) (L : ℝ) (q : V → Fin s → Option W)
    (hD : ∀ w, H.degree w ≤ D)
    (hnear : ∀ v, q v ∈ starWitnessTuples H (f v) s)
    (hcapacity : ∀ v, 0 < starWitnessCapacity J P (q v) ∧ starWitnessCapacity J P (q v) ≤ P)
    (hdeficit : 2 * L ≤ ∑ v,
      ((copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q v))) :
    copyRawEdges f ∈ starImagePatterns H J (copyVertices f) s G.edgeSet.ncard D P L := by
  classical
  let e := copyVertexEquiv f
  let q' := fun u : copyVertices f => q (e.symm u)
  have hq' : q' ∈ validStarWitnesses H J (copyVertices f) s P := by
    apply (mem_validStarWitnesses H J (copyVertices f) s P q').mpr
    constructor
    · intro u
      have h := hnear (e.symm u)
      rwa [copyVertexEquiv_symm_apply] at h
    · intro u
      exact hcapacity (e.symm u)
  have hU : (copyVertices f).Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨f v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  apply starPattern_mem_of_intersection_deficit H J (copyVertices f) (copyRawEdges f)
    s G.edgeSet.ncard D P L hU (copyRawEdges_subset_inducedHostEdges f) (copyRawEdges_card f) hD q' hq'
  have hsum := e.sum_comp (fun u : copyVertices f =>
    ((copyRawEdges f ∩ starWitnessEdges J u.val (q' u)).card : ℝ) *
      Real.log ((P : ℝ) / starWitnessCapacity J P (q' u)))
  have hleft : (∑ v,
      ((copyRawEdges f ∩ starWitnessEdges J (e v).val (q' (e v))).card : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q' (e v)))) =
      ∑ v, ((copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [q']
    rw [e.symm_apply_apply]
    rfl
  rw [hleft] at hsum
  exact hsum ▸ hdeficit

end Erdos911
