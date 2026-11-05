import Erdos911.CopyDensity
import Erdos911.NearRegularRamsey
import Erdos911.IncidenceRamsey

namespace Erdos911

theorem near_regular_size_ramsey_lower_bound_general (A M C : ℝ)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (Δ : ℕ) (G : SimpleGraph V), 0 < Fintype.card V →
      (∀ v, d ≤ (G.neighborSet v).ncard) → (∀ v, (G.neighborSet v).ncard ≤ Δ) →
      (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
      (∀ S : Finset V, S.card ≤ 2 * nearRegularBlockSize d →
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨d₀, hd₀⟩ := near_regular_size_ramsey_lower_bound A M C hA hM hC
  refine ⟨d₀, ?_⟩
  intro d hd V _ _ Δ G hV hmin hmax hdegree hlocal
  classical
  let G' := G.comap (Fintype.equivFin V).symm
  let e : G' ≃g G := SimpleGraph.Iso.comap (Fintype.equivFin V).symm G
  have hdeg : ∀ v, (G'.neighborSet v).ncard = (G.neighborSet (e v)).ncard := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using (e.degree_eq v).symm
  have he : G'.edgeSet.ncard = G.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using e.card_edgeFinset_eq
  have hr := sizeRamsey_self_eq_of_iso e
  have hlocal' := induced_density_of_copy e.toCopy (2 * nearRegularBlockSize d) (C * Real.log d) hlocal
  have h := hd₀ d hd (Fintype.card V) Δ G' hV
    (fun v => by rw [hdeg]; exact hmin _) (fun v => by rw [hdeg]; exact hmax _) hdegree hlocal'
  simpa only [he, hr] using h

theorem incidence_size_ramsey_lower_bound_general (B : ℕ) (M C τ : ℝ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) (hτ : 0 < τ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ G : SimpleGraph V, 0 < Fintype.card V →
      (∀ v, d ≤ (G.neighborSet v).ncard) → (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      (∀ S : Finset V, S.card ≤ 2 * nearRegularBlockSize d →
        ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      ∀ left right : Finset V, G.IsBipartiteWith (left : Set V) (right : Set V) →
      (∀ v ∈ right, (G.neighborSet v).ncard = d) →
      (∀ v ∈ left, (d : ℝ) * (Real.log d) ^ τ ≤ (G.neighborSet v).ncard) →
      (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨d₀, hd₀⟩ := incidence_size_ramsey_lower_bound B M C τ hM hC hτ
  refine ⟨d₀, ?_⟩
  intro d hd V _ _ G hV hmin hmax hlocal left right hBip hright hleft
  classical
  let G' := G.comap (Fintype.equivFin V).symm
  let e : G' ≃g G := SimpleGraph.Iso.comap (Fintype.equivFin V).symm G
  let left' := left.image e.symm
  let right' := right.image e.symm
  have hdeg : ∀ v, (G'.neighborSet v).ncard = (G.neighborSet (e v)).ncard := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using (e.degree_eq v).symm
  have he : G'.edgeSet.ncard = G.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using e.card_edgeFinset_eq
  have hr := sizeRamsey_self_eq_of_iso e
  have hmemL (v) : v ∈ left' ↔ e v ∈ left := mem_image_equiv_symm e.toEquiv left v
  have hmemR (v) : v ∈ right' ↔ e v ∈ right := mem_image_equiv_symm e.toEquiv right v
  have hBip' : G'.IsBipartiteWith (left' : Set _) (right' : Set _) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro v hvL hvR
      exact Set.disjoint_left.mp hBip.disjoint ((hmemL v).mp hvL) ((hmemR v).mp hvR)
    · intro u v huv
      rcases hBip.mem_of_adj (e.map_rel_iff.mpr huv) with h | h
      · exact Or.inl ⟨(hmemL u).mpr h.1, (hmemR v).mpr h.2⟩
      · exact Or.inr ⟨(hmemR u).mpr h.1, (hmemL v).mpr h.2⟩
  have hlocal' := induced_density_of_copy e.toCopy (2 * nearRegularBlockSize d) (C * Real.log d) hlocal
  have h := hd₀ d hd (Fintype.card V) G' hV
    (fun v => by rw [hdeg]; exact hmin _) (fun v => by rw [hdeg]; exact hmax _) hlocal'
    left' right' hBip' (fun v hv => by rw [hdeg]; exact hright _ ((hmemR v).mp hv))
    (fun v hv => by rw [hdeg]; exact hleft _ ((hmemL v).mp hv))
  simpa only [he, hr] using h

end Erdos911
