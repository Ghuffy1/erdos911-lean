import Erdos911.GlobalDensityBound
import Erdos911.LowEndpointDensity

namespace Erdos911

def lowEndpointPrunedGraph {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) : SimpleGraph W where
  Adj u v := H.Adj u v ∧ (H.degree u ≤ T ∨ H.degree v ≤ T)
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := H.irrefl h.1

instance {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) :
    DecidableRel (lowEndpointPrunedGraph H T).Adj := by
  unfold lowEndpointPrunedGraph
  infer_instance

theorem lowEndpointPrunedGraph_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) : lowEndpointPrunedGraph H T ≤ H :=
  fun _ _ h => h.1

theorem lowEndpointPrunedGraph_low_degree {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) :
    ∀ u v, (lowEndpointPrunedGraph H T).Adj u v →
      (lowEndpointPrunedGraph H T).degree u ≤ T ∨ (lowEndpointPrunedGraph H T).degree v ≤ T := by
  intro u v huv
  let hcopy := SimpleGraph.Copy.ofLE _ H (lowEndpointPrunedGraph_le H T)
  have hdegree (w : W) : (lowEndpointPrunedGraph H T).degree w ≤ H.degree w := by
    have h := hcopy.degree_le w
    change (lowEndpointPrunedGraph H T).degree w ≤ H.degree w at h
    exact h
  exact huv.2.imp (fun h => (hdegree u).trans h) (fun h => (hdegree v).trans h)

theorem lowEndpointPrunedGraph_induced_density {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) (S : Finset W) :
    ((lowEndpointPrunedGraph H T).induce (S : Set W)).edgeSet.ncard ≤ T * S.card :=
  induced_edges_le_low_endpoint_degree _ T (lowEndpointPrunedGraph_low_degree H T) S

theorem copyHostEdges_retained_inter_card {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : G.Copy H) (E : Finset (Sym2 W)) :
    (copyHostEdges f ∩ retainedEdges H E).card = (copyRawEdges f ∩ E).card := by
  classical
  have heq : (copyHostEdges f ∩ retainedEdges H E).map ⟨Subtype.val, Subtype.val_injective⟩ =
      copyRawEdges f ∩ E := by
    ext e
    constructor
    · intro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_map.mpr ⟨a, (Finset.mem_inter.mp ha).1, rfl⟩,
          (mem_retainedEdges H E a).mp (Finset.mem_inter.mp ha).2⟩
    · intro he
      obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp (Finset.mem_inter.mp he).1
      refine Finset.mem_map.mpr ⟨a, Finset.mem_inter.mpr ⟨ha, ?_⟩, hea⟩
      apply (mem_retainedEdges H E a).mpr
      change a.val = e at hea
      rw [hea]
      exact (Finset.mem_inter.mp he).2
  rw [← heq, Finset.card_map]

/-- Deleting edges whose two endpoints both have high host degree costs
only the target's hereditary density times the number of high vertices. -/
theorem high_high_pruning_copy_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hlocal : ∀ S : Finset V, ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (f : G.Copy H) :
    ((copyRawEdges f ∩ (H \ lowEndpointPrunedGraph H T).edgeFinset).card : ℝ) ≤
      2 * σ * H.edgeFinset.card / ((T + 1 : ℕ) : ℝ) := by
  classical
  let S := Finset.univ.filter (fun w => T < H.degree w)
  let E := (H \ lowEndpointPrunedGraph H T).edgeFinset
  have hsupport : ∀ u v (h : H.Adj u v),
      (⟨s(u, v), h⟩ : H.edgeSet) ∈ retainedEdges H E → u ∈ S ∧ v ∈ S := by
    intro u v h he
    have hE := (mem_retainedEdges H E ⟨s(u, v), h⟩).mp he
    have hnot : ¬(H.degree u ≤ T ∨ H.degree v ≤ T) := by
      have hdeleted := (H \ lowEndpointPrunedGraph H T).mem_edgeFinset.mp hE
      exact fun hn => hdeleted.2 ⟨h, hn⟩
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  have hcount := copyHostEdges_supported_card_le f S (retainedEdges H E) hsupport
  rw [copyHostEdges_retained_inter_card] at hcount
  have hpre : ((copyVertexPreimage f S).card : ℝ) ≤ S.card := by
    exact_mod_cast copyVertexPreimage_card_le f S
  have hS : (S.card : ℝ) ≤ 2 * H.edgeFinset.card / ((T + 1 : ℕ) : ℝ) := by
    simpa only [S, Nat.succ_le_iff] using high_degree_card_bound_real H (T + 1) (by omega)
  calc
    ((copyRawEdges f ∩ (H \ lowEndpointPrunedGraph H T).edgeFinset).card : ℝ) ≤
        (G.induce (copyVertexPreimage f S : Set V)).edgeSet.ncard := by exact_mod_cast hcount
    _ ≤ σ * (copyVertexPreimage f S).card := hlocal _
    _ ≤ σ * S.card := mul_le_mul_of_nonneg_left hpre hσ
    _ ≤ σ * (2 * H.edgeFinset.card / ((T + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hS hσ
    _ = _ := by ring

theorem high_high_pruning_budget {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (T : ℕ) (σ Λ : ℝ) (hσ : 0 ≤ σ)
    (hlocal : ∀ S : Finset V, ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hhost : (H.edgeFinset.card : ℝ) ≤ Λ * G.edgeSet.ncard)
    (hscale : 16 * Λ * σ ≤ ((T + 1 : ℕ) : ℝ)) (f : G.Copy H) :
    ((copyRawEdges f ∩ (H \ lowEndpointPrunedGraph H T).edgeFinset).card : ℝ) ≤
      (G.edgeSet.ncard : ℝ) / 8 := by
  apply (high_high_pruning_copy_capacity G H T σ hσ hlocal f).trans
  have hden : (0 : ℝ) < (T + 1 : ℕ) := by positivity
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hhost (show 0 ≤ 2 * σ by positivity)
  have hs := mul_le_mul_of_nonneg_right hscale
    (Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard)
  nlinarith only [hm, hs]

end Erdos911
