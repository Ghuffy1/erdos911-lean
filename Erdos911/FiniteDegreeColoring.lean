import Erdos911.GraphCounting

namespace Erdos911

noncomputable def monochromaticVertices {V A : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → A) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ w, G.Adj v w ∧ f v = f w)

theorem mem_monochromaticVertices {V A : Type*} [Fintype V]
    (G : SimpleGraph V) (f : V → A) (v : V) :
    v ∈ monochromaticVertices G f ↔ ∃ w, G.Adj v w ∧ f v = f w := by
  classical
  simp only [monochromaticVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A finite graph of maximum degree at most D has a proper labeling
with D+1 labels. The proof minimizes the number of conflicted vertices. -/
theorem exists_degree_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    ∃ c : V → Fin (D + 1), ∀ u v, G.Adj u v → c u ≠ c v := by
  classical
  obtain ⟨c, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (V → Fin (D + 1)))
    (fun c => (monochromaticVertices G c).card) Finset.univ_nonempty
  have hempty : monochromaticVertices G c = ∅ := by
    by_contra hne
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    let used := (G.neighborFinset v).image c
    have hcard : used.card < (Finset.univ : Finset (Fin (D + 1))).card := by
      calc
        used.card ≤ (G.neighborFinset v).card := Finset.card_image_le
        _ = G.degree v := G.card_neighborFinset_eq_degree v
        _ ≤ D := hD v
        _ < D + 1 := Nat.lt_succ_self D
        _ = _ := by simp
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    let c' := Function.update c v a
    have hproperAt (w : V) (hvw : G.Adj v w) : c' v ≠ c' w := by
      intro heq
      have hwv : w ≠ v := hvw.ne.symm
      have heq' : c w = a := by simpa [c', hwv] using heq.symm
      exact ha (Finset.mem_image.mpr ⟨w, (G.mem_neighborFinset v w).mpr hvw, heq'⟩)
    have hsub : monochromaticVertices G c' ⊆ (monochromaticVertices G c).erase v := by
      intro u hu
      obtain ⟨w, huw, hcolors⟩ := (mem_monochromaticVertices G c' u).mp hu
      have huv : u ≠ v := by
        intro h
        subst u
        exact hproperAt w huw hcolors
      have hwv : w ≠ v := by
        intro h
        subst w
        exact hproperAt u huw.symm hcolors.symm
      refine Finset.mem_erase.mpr ⟨huv, (mem_monochromaticVertices G c u).mpr ⟨w, huw, ?_⟩⟩
      simpa [c', huv, hwv] using hcolors
    have hless := Finset.card_lt_card (Finset.erase_ssubset hv)
    have hle := (hmin c' (Finset.mem_univ _)).trans (Finset.card_le_card hsub)
    omega
  refine ⟨c, ?_⟩
  intro u v huv heq
  have h := (mem_monochromaticVertices G c u).mpr ⟨v, huv, heq⟩
  rw [hempty] at h
  exact Finset.notMem_empty _ h

def twoStepGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v)
  symm.symm _ _ h := ⟨h.1.symm, h.2.elim (fun h => Or.inl h.symm)
    (fun ⟨w, huw, hwv⟩ => Or.inr ⟨w, hwv.symm, huw.symm⟩)⟩
  loopless.irrefl _ h := h.1 rfl

theorem twoStepGraph_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (v : V) :
    letI : DecidableRel (twoStepGraph G).Adj := Classical.decRel _
    (twoStepGraph G).degree v ≤ D * (D + 1) := by
  classical
  have hsub : (twoStepGraph G).neighborFinset v ⊆ G.neighborFinset v ∪
      (G.neighborFinset v).biUnion (fun w => G.neighborFinset w) := by
    intro u hu
    have h := ((twoStepGraph G).mem_neighborFinset v u).mp hu
    rcases h.2 with h | ⟨w, hvw, hwu⟩
    · exact Finset.mem_union_left _ ((G.mem_neighborFinset v u).mpr h)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨w, (G.mem_neighborFinset v w).mpr hvw, (G.mem_neighborFinset w u).mpr hwu⟩)
  have hsum : ((G.neighborFinset v).biUnion (fun w => G.neighborFinset w)).card ≤ D * D := by
    calc
      _ ≤ ∑ w ∈ G.neighborFinset v, (G.neighborFinset w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ G.neighborFinset v, D := Finset.sum_le_sum (fun w _ => by
        simpa only [G.card_neighborFinset_eq_degree] using hD w)
      _ = G.degree v * D := by simp
      _ ≤ D * D := Nat.mul_le_mul_right D (hD v)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [(twoStepGraph G).card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at h
  have hv := hD v
  nlinarith only [h, hsum, hv]

theorem exists_two_step_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    ∃ c : V → Fin (D * (D + 1) + 1),
      (∀ u v, G.Adj u v → c u ≠ c v) ∧
      (∀ u v w, G.Adj u v → G.Adj u w → c v = c w → v = w) := by
  classical
  obtain ⟨c, hc⟩ := exists_degree_coloring (twoStepGraph G) (D * (D + 1))
    (twoStepGraph_degree_le G D hD)
  refine ⟨c, ?_, ?_⟩
  · intro u v huv
    exact hc u v ⟨huv.ne, Or.inl huv⟩
  · intro u v w huv huw heq
    by_contra hne
    exact hc v w ⟨hne, Or.inr ⟨u, huv.symm, huw⟩⟩ heq

end Erdos911
