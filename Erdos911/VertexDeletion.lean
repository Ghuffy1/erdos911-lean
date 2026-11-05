import Erdos911.CopyDensity
import Erdos911.MarkedNeighborhoodStars

namespace Erdos911

def vertexDeletedGraph {V : Type*} (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl v h := G.loopless.irrefl v h.1

theorem edge_ncard_induce_of_support_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : G.support ⊆ S) :
    (G.induce S).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  rw [← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card,
    ← Set.fintypeCard_eq_ncard, ← SimpleGraph.edgeFinset_card]
  exact G.card_edgeFinset_induce_of_support_subset hS

/-- Deleting a vertex set costs at most its order times the maximum degree. -/
theorem vertex_deletion_edge_cost {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (Δ : ℕ)
    (hmax : ∀ v, G.degree v ≤ Δ) :
    G.edgeSet.ncard ≤ (G.induce (↑S : Set V)ᶜ).edgeSet.ncard + S.card * Δ := by
  classical
  let J := vertexDeletedGraph G S
  let E := incidentEdgesAtSet G S
  have hE : E ⊆ G.edgeFinset := by
    intro e he
    exact ((mem_incidentEdgesAtSet_iff G S e).mp he).1
  have heq : J.edgeFinset = G.edgeFinset \ E := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Finset.mem_sdiff, E, mem_incidentEdgesAtSet_iff, SimpleGraph.mem_edgeFinset]
      change (G.Adj u v ∧ u ∉ S ∧ v ∉ S) ↔
        G.Adj u v ∧ ¬(G.Adj u v ∧ ∃ x ∈ S, x ∈ s(u, v))
      simp only [Sym2.mem_iff, and_or_left, exists_or, exists_eq_right]
      tauto
  have hcount : G.edgeSet.ncard = J.edgeSet.ncard + E.card := by
    have h := Finset.card_sdiff_add_card_eq_card hE
    rw [← heq, G.edgeFinset_card, J.edgeFinset_card, Set.fintypeCard_eq_ncard,
      Set.fintypeCard_eq_ncard] at h
    exact h.symm
  have hsupp : J.support ⊆ (↑S : Set V)ᶜ := fun _ ⟨_, h⟩ => h.2.1
  have hind : J.induce (↑S : Set V)ᶜ = G.induce (↑S : Set V)ᶜ := by
    ext u v
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, u.property, v.property⟩
  have hsame : J.edgeSet.ncard = (G.induce (↑S : Set V)ᶜ).edgeSet.ncard := by
    rw [← hind, edge_ncard_induce_of_support_subset J _ hsupp]
  rw [hcount, hsame]
  exact Nat.add_le_add_left (incidentEdgesAtSet_card_le G S Δ hmax) _

theorem complement_induced_local_density {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (K : ℕ) (σ : ℝ)
    (hlocal : ∀ T : Finset V, Disjoint T S → T.card ≤ K →
      ((G.induce (T : Set V)).edgeSet.ncard : ℝ) ≤ σ * T.card) :
    ∀ T : Finset ↥(↑S : Set V)ᶜ, T.card ≤ K →
      (((G.induce (↑S : Set V)ᶜ).induce (T : Set ↥(↑S : Set V)ᶜ)).edgeSet.ncard : ℝ) ≤
        σ * T.card := by
  classical
  intro T hT
  let f := SimpleGraph.Copy.induce G (↑S : Set V)ᶜ
  have hcard : (T.image f).card = T.card := Finset.card_image_of_injective T f.injective
  have hdisjoint : Disjoint (T.image f) S := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.property hvS
  have h := hlocal (T.image f) hdisjoint (by simpa only [hcard] using hT)
  rw [hcard] at h
  apply le_trans _ h
  exact_mod_cast copy_edge_ncard_le (copyInduceImage f T)

end Erdos911
