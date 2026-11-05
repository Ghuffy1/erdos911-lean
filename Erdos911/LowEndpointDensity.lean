import Erdos911.GraphCounting

namespace Erdos911

/-- A low-degree endpoint on every edge controls total edge density. -/
theorem edges_le_low_endpoint_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hlow : ∀ u v, G.Adj u v → G.degree u ≤ D ∨ G.degree v ≤ D) :
    G.edgeFinset.card ≤ D * Fintype.card V := by
  classical
  let S := Finset.univ.filter (fun v => G.degree v ≤ D)
  have hcover : G.IsVertexCover (S : Set V) := by
    intro u v huv
    rcases hlow u v huv with hu | hv
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
  have hdegree : ∀ v ∈ S, G.degree v ≤ D := fun _ hv => (Finset.mem_filter.mp hv).2
  have hS : S.card ≤ Fintype.card V := Finset.card_le_univ _
  have h := edges_le_cover_card_mul_degree_on G S D hcover hdegree
  simpa only [Nat.mul_comm] using h.trans (Nat.mul_le_mul_right D hS)

/-- The low-endpoint density bound is inherited by every induced subgraph. -/
theorem induced_edges_le_low_endpoint_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hlow : ∀ u v, G.Adj u v → G.degree u ≤ D ∨ G.degree v ≤ D)
    (U : Finset V) :
    (G.induce (U : Set V)).edgeSet.ncard ≤ D * U.card := by
  classical
  let H := G.induce (U : Set V)
  have hH : ∀ u v, H.Adj u v → H.degree u ≤ D ∨ H.degree v ≤ D := by
    intro u v huv
    rcases hlow u.val v.val huv with hu | hv
    · exact Or.inl (((SimpleGraph.Copy.induce G (U : Set V)).degree_le u).trans hu)
    · exact Or.inr (((SimpleGraph.Copy.induce G (U : Set V)).degree_le v).trans hv)
  have hbound := edges_le_low_endpoint_degree H D hH
  have hcard : Fintype.card (U : Set V) = U.card := by simp
  rw [hcard] at hbound
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hbound

end Erdos911
