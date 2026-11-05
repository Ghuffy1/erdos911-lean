import Erdos911.StarImagePatterns

namespace Erdos911

noncomputable def copyVertexEquiv {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) : V ≃ copyVertices f :=
  Equiv.ofBijective (fun v => ⟨f v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩) (by
    constructor
    · intro u v huv
      exact f.injective (congrArg Subtype.val huv)
    · intro w
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp w.property
      exact ⟨v, Subtype.ext hv⟩)

theorem copyVertexEquiv_apply_val {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (v : V) :
    (copyVertexEquiv f v).val = f v := rfl

theorem copyVertexEquiv_symm_apply {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (u : copyVertices f) :
    f ((copyVertexEquiv f).symm u) = u.val :=
  congrArg Subtype.val ((copyVertexEquiv f).apply_symm_apply u)

theorem copy_edgeRoleDegree {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) (f : G.Copy H) (v : V) :
    edgeRoleDegree (copyRawEdges f) (f v) = G.degree v := by
  classical
  have hf : Function.Injective (f : V → W) := f.injective
  have hmemmap (a : Sym2 V) : f v ∈ Sym2.map (f : V → W) a ↔ v ∈ a := by
    rw [Sym2.mem_map]
    constructor
    · rintro ⟨u, hu, huv⟩
      exact hf huv ▸ hu
    · intro hv
      exact ⟨v, hv, rfl⟩
  have hfilter : (copyRawEdges f).filter (fun e => f v ∈ e) =
      (G.incidenceFinset v).image (Sym2.map (f : V → W)) := by
    ext e
    constructor
    · intro he
      obtain ⟨heF, hev⟩ := Finset.mem_filter.mp he
      obtain ⟨a, hae⟩ := (mem_copyRawEdges_iff_exists f e).mp heF
      apply Finset.mem_image.mpr
      refine ⟨a.val, ?_, hae⟩
      rw [G.incidenceFinset_eq_filter]
      refine Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr a.property, ?_⟩
      apply (hmemmap a.val).mp
      rwa [hae]
    · intro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      rw [G.incidenceFinset_eq_filter] at ha
      obtain ⟨haG, hav⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      exact ⟨(mem_copyRawEdges_iff_exists f _).mpr
        ⟨⟨a, SimpleGraph.mem_edgeFinset.mp haG⟩, rfl⟩, (hmemmap a).mpr hav⟩
  unfold edgeRoleDegree
  rw [hfilter, Finset.card_image_of_injective _ (Sym2.map.injective hf),
    G.card_incidenceFinset_eq_degree]

/-- Witnesses chosen on the original target vertices transfer to the
image-based bad-copy predicate without changing degrees or deficit sums. -/
theorem copy_star_deficit_of_witnesses {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : G.Copy H) (s P : ℕ) (L : ℝ) (q : V → Fin s → Option W)
    (hnear : ∀ v, q v ∈ starWitnessTuples H (f v) s)
    (hcapacity : ∀ v, 0 < starWitnessCapacity J P (q v) ∧ starWitnessCapacity J P (q v) ≤ P)
    (hcoverage : ∀ v, (G.degree v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) ≤
      2 * (copyRawEdges f ∩ starWitnessEdges J (f v) (q v)).card *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q v)))
    (hdeficit : 4 * L ≤ ∑ v, (G.degree v : ℝ) *
      Real.log ((P : ℝ) / starWitnessCapacity J P (q v))) :
    IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P L := by
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
  refine ⟨q', hq', ?_, ?_⟩
  · intro u
    have h := hcoverage (e.symm u)
    rw [← copy_edgeRoleDegree G H f (e.symm u), copyVertexEquiv_symm_apply] at h
    exact h
  · have hsum := e.sum_comp (fun u : copyVertices f =>
      (edgeRoleDegree (copyRawEdges f) u.val : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q' u)))
    have hleft : (∑ v, (edgeRoleDegree (copyRawEdges f) (e v).val : ℝ) *
        Real.log ((P : ℝ) / starWitnessCapacity J P (q' (e v)))) =
          ∑ v, (G.degree v : ℝ) * Real.log ((P : ℝ) / starWitnessCapacity J P (q v)) := by
      apply Finset.sum_congr rfl
      intro v _
      dsimp only [q']
      rw [e.symm_apply_apply]
      change (edgeRoleDegree (copyRawEdges f) (f v) : ℝ) * _ = _
      rw [copy_edgeRoleDegree]
    rw [hleft] at hsum
    exact hsum ▸ hdeficit

end Erdos911
