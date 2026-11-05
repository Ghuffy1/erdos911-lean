import Erdos911.StarWitnessCounting

namespace Erdos911

def inactiveStarTuple {W : Type*} {s : ℕ} (q : Fin s → Option W) : Prop := ∀ i, q i = none

noncomputable def tupleCommonNeighbors {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] {s : ℕ} (q : Fin s → Option W) : Finset W := by
  classical
  exact Finset.univ.filter (fun z => ∀ i x, q i = some x → J.Adj x z)

noncomputable def starWitnessCapacity {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (P : ℕ) {s : ℕ} (q : Fin s → Option W) : ℕ := by
  classical
  exact if inactiveStarTuple q then P else (tupleCommonNeighbors J q).card

noncomputable def starWitnessEdges {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (v : W) {s : ℕ}
    (q : Fin s → Option W) : Finset (Sym2 W) := by
  classical
  exact if inactiveStarTuple q then ∅ else (tupleCommonNeighbors J q).image (fun z => s(v, z))

theorem starWitnessEdges_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (P : ℕ) (v : W) {s : ℕ}
    (q : Fin s → Option W) : (starWitnessEdges J v q).card ≤ starWitnessCapacity J P q := by
  classical
  unfold starWitnessEdges starWitnessCapacity
  split_ifs
  · simp only [Finset.card_empty, Nat.zero_le]
  · exact Finset.card_image_le

theorem starWitnessEdges_incident {W : Type*} [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) [DecidableRel J.Adj] (v : W) {s : ℕ}
    (q : Fin s → Option W) (e : Sym2 W) (he : e ∈ starWitnessEdges J v q) : v ∈ e := by
  classical
  unfold starWitnessEdges at he
  split_ifs at he
  · exact (Finset.notMem_empty e he).elim
  · obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp he
    simp

noncomputable def validStarWitnesses {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (s P : ℕ) : Finset (U → Fin s → Option W) := by
  classical
  exact (Fintype.piFinset (fun v : U => starWitnessTuples H v.val s)).filter
    (fun q => ∀ v : U, 0 < starWitnessCapacity J P (q v) ∧ starWitnessCapacity J P (q v) ≤ P)

theorem mem_validStarWitnesses {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (U : Finset W) (s P : ℕ) (q : U → Fin s → Option W) :
    q ∈ validStarWitnesses H J U s P ↔
      (∀ v : U, q v ∈ starWitnessTuples H v.val s) ∧
      ∀ v : U, 0 < starWitnessCapacity J P (q v) ∧ starWitnessCapacity J P (q v) ≤ P := by
  classical
  simp only [validStarWitnesses, Finset.mem_filter, Fintype.mem_piFinset]

theorem validStarWitnesses_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (D : ℕ) (hD : ∀ w, H.degree w ≤ D) (U : Finset W) (s P : ℕ) :
    (validStarWitnesses H J U s P).card ≤ (D ^ 2 + 1) ^ (s * U.card) := by
  classical
  exact (Finset.card_filter_le _ _).trans (starWitnessConfigurations_card_le H D hD U s)

noncomputable def edgeRoleDegree {W : Type*} [DecidableEq W]
    (F : Finset (Sym2 W)) (v : W) : ℕ := by
  classical
  exact (F.filter (fun e => v ∈ e)).card

theorem incident_subset_card_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (F : Finset (Sym2 W)) (v : W)
    (hF : F ⊆ H.edgeFinset) (hincident : ∀ e ∈ F, v ∈ e) : F.card ≤ H.degree v := by
  apply (Finset.card_le_card (show F ⊆ H.incidenceFinset v from ?_)).trans_eq
    (H.card_incidenceFinset_eq_degree v)
  intro e he
  rw [H.incidenceFinset_eq_filter]
  exact Finset.mem_filter.mpr ⟨hF he, hincident e he⟩

theorem edgeRoleDegree_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (F : Finset (Sym2 W)) (v : W)
    (hF : F ⊆ H.edgeFinset) : edgeRoleDegree F v ≤ H.degree v := by
  classical
  exact incident_subset_card_le_degree H (F.filter (fun e => v ∈ e)) v
    (Finset.filter_subset _ _ |>.trans hF) (fun e he => (Finset.mem_filter.mp he).2)

end Erdos911
