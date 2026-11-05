import Erdos911.HighHighPruning
import Erdos911.DeletedEdgeCapacity

namespace Erdos911

theorem copy_deleted_capacity_inf {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj] (f : G.Copy H) :
    (copyRawEdges f ∩ (H \ (J ⊓ K)).edgeFinset).card ≤
      (copyRawEdges f ∩ (H \ J).edgeFinset).card +
      (copyRawEdges f ∩ (H \ K).edgeFinset).card := by
  classical
  have hsub : (H \ (J ⊓ K)).edgeFinset ⊆ (H \ J).edgeFinset ∪ (H \ K).edgeFinset := by
    intro e
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_inf,
      Set.mem_sdiff, Set.mem_inter_iff, Finset.mem_union]
    tauto
  exact (Finset.card_le_card (Finset.inter_subset_inter_left hsub)).trans
    (copy_capacity_union_inter (copyRawEdges f) (H \ J).edgeFinset (H \ K).edgeFinset)

theorem copy_deleted_capacity_delete_inter {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (E : Finset (Sym2 W)) (f : G.Copy H) :
    (copyRawEdges f ∩ (H \ J.deleteEdges (E : Set (Sym2 W))).edgeFinset).card ≤
      (copyRawEdges f ∩ (H \ J).edgeFinset).card + (copyRawEdges f ∩ E).card := by
  classical
  have hsub : (H \ J.deleteEdges (E : Set (Sym2 W))).edgeFinset ⊆ (H \ J).edgeFinset ∪ E := by
    intro e
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Finset.mem_coe, Finset.mem_union]
    tauto
  exact (Finset.card_le_card (Finset.inter_subset_inter_left hsub)).trans
    (copy_capacity_union_inter (copyRawEdges f) (H \ J).edgeFinset E)

theorem copy_deleted_capacity_delete {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (E : Finset (Sym2 W)) (f : G.Copy H) :
    (copyRawEdges f ∩ (H \ J.deleteEdges (E : Set (Sym2 W))).edgeFinset).card ≤
      (copyRawEdges f ∩ (H \ J).edgeFinset).card + E.card := by
  exact (copy_deleted_capacity_delete_inter G H J E f).trans
    (Nat.add_le_add_left (Finset.card_le_card Finset.inter_subset_right) _)

theorem pruning_scaled_fraction_bound (e m Λ σ ε : ℝ) (T : ℕ) (he : 0 ≤ e) (hσ : 0 ≤ σ)
    (hm : m ≤ Λ * e) (hscale : 32 * Λ * σ ≤ ε * ((T + 1 : ℕ) : ℝ)) :
    2 * σ * m / ((T + 1 : ℕ) : ℝ) ≤ ε * e / 16 := by
  have hden : (0 : ℝ) < (T + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hden).mpr
  have hfirst := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * σ by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hscale he
  nlinarith only [hfirst, hsecond]

theorem pruning_fraction_bound (e m Λ σ : ℝ) (T : ℕ) (he : 0 ≤ e) (hσ : 0 ≤ σ)
    (hm : m ≤ Λ * e) (hscale : 32 * Λ * σ ≤ ((T + 1 : ℕ) : ℝ)) :
    2 * σ * m / ((T + 1 : ℕ) : ℝ) ≤ e / 16 := by
  simpa only [one_mul] using pruning_scaled_fraction_bound e m Λ σ 1 T he hσ hm
    (by simpa only [one_mul] using hscale)

/-- Simultaneously bounding maximum degree and induced density loses at
most a prescribed fraction of the target in each original-host copy. -/
theorem bounded_sparse_host_pruning_scaled {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (Δ D T : ℕ) (σ Λ ε : ℝ)
    (hmax : ∀ v, G.degree v ≤ Δ) (hσ : 0 ≤ σ)
    (hlocal : ∀ S : Finset V, ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hdegreeScale : 32 * Λ * Δ ≤ ε * ((D + 1 : ℕ) : ℝ))
    (hdensityScale : 32 * Λ * σ ≤ ε * ((T + 1 : ℕ) : ℝ)) :
    ∃ J : SimpleGraph W, J ≤ H ∧ (∀ w, (J.neighborSet w).ncard ≤ D) ∧
      (∀ S : Finset W, (J.induce (S : Set W)).edgeSet.ncard ≤ T * S.card) ∧
      ∀ f : G.Copy H, ((copyRawEdges f ∩ (H \ J).edgeSet.toFinite.toFinset).card : ℝ) ≤
        ε * (G.edgeSet.ncard : ℝ) / 8 := by
  classical
  let J := degreePrunedGraph H D ⊓ lowEndpointPrunedGraph H T
  have hJdegree : J ≤ degreePrunedGraph H D := inf_le_left
  have hJdensity : J ≤ lowEndpointPrunedGraph H T := inf_le_right
  have hJH : J ≤ H := hJdegree.trans (degreePrunedGraph_le H D)
  refine ⟨J, hJH, ?_, ?_, ?_⟩
  · intro w
    have h : J.degree w ≤ (degreePrunedGraph H D).degree w :=
      (SimpleGraph.Copy.ofLE J (degreePrunedGraph H D) hJdegree).degree_le w
    simpa only [J.ncard_neighborSet] using h.trans (degreePrunedGraph_degree_le H D w)
  · intro S
    have hsub : J.induce (S : Set W) ≤ (lowEndpointPrunedGraph H T).induce (S : Set W) :=
      fun _ _ h => hJdensity h
    exact (copy_edge_ncard_le (SimpleGraph.Copy.ofLE _ _ hsub)).trans
      (lowEndpointPrunedGraph_induced_density H T S)
  · intro f
    have hsplit : ((copyRawEdges f ∩ (H \ J).edgeFinset).card : ℝ) ≤
        (copyRawEdges f ∩ (H \ degreePrunedGraph H D).edgeFinset).card +
        (copyRawEdges f ∩ (H \ lowEndpointPrunedGraph H T).edgeFinset).card := by
      exact_mod_cast copy_deleted_capacity_inf G H (degreePrunedGraph H D) (lowEndpointPrunedGraph H T) f
    have hdegreeBudget := pruning_scaled_fraction_bound (G.edgeSet.ncard : ℝ) H.edgeFinset.card Λ Δ ε D
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hhost hdegreeScale
    have hdegree := (degreePruned_copy_deleted_capacity G H f Δ D hmax).trans
      (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hdegreeBudget)
    have hdensity := (high_high_pruning_copy_capacity G H T σ hσ hlocal f).trans
      (pruning_scaled_fraction_bound (G.edgeSet.ncard : ℝ) H.edgeFinset.card Λ σ ε T
        (Nat.cast_nonneg _) hσ hhost hdensityScale)
    have heq : (H \ J).edgeSet.toFinite.toFinset = (H \ J).edgeFinset := by
      ext e
      simp only [Set.Finite.mem_toFinset, SimpleGraph.mem_edgeFinset]
    rw [heq]
    linarith

theorem bounded_sparse_host_pruning {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (Δ D T : ℕ) (σ Λ : ℝ)
    (hmax : ∀ v, G.degree v ≤ Δ) (hσ : 0 ≤ σ)
    (hlocal : ∀ S : Finset V, ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hdegreeScale : 32 * Λ * Δ ≤ ((D + 1 : ℕ) : ℝ))
    (hdensityScale : 32 * Λ * σ ≤ ((T + 1 : ℕ) : ℝ)) :
    ∃ J : SimpleGraph W, J ≤ H ∧ (∀ w, (J.neighborSet w).ncard ≤ D) ∧
      (∀ S : Finset W, (J.induce (S : Set W)).edgeSet.ncard ≤ T * S.card) ∧
      ∀ f : G.Copy H, ((copyRawEdges f ∩ (H \ J).edgeSet.toFinite.toFinset).card : ℝ) ≤
        (G.edgeSet.ncard : ℝ) / 8 := by
  simpa only [one_mul] using bounded_sparse_host_pruning_scaled G H Δ D T σ Λ 1 hmax hσ hlocal hhost
    (by simpa only [one_mul] using hdegreeScale) (by simpa only [one_mul] using hdensityScale)

end Erdos911
