import Erdos911.IncidenceCapacity
import Erdos911.NearRegularHostParameters

namespace Erdos911

noncomputable def incidenceRightCutoff (M : ℝ) (d : ℕ) : ℕ := Nat.ceil (32 * M * d * d)

def incidencePrunedHost {W : Type*} [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj]
    (D T : ℕ) : SimpleGraph W := degreePrunedGraph K D ⊓ lowEndpointPrunedGraph K T

instance {W : Type*} [Fintype W] (K : SimpleGraph W) [DecidableRel K.Adj] (D T : ℕ) :
    DecidableRel (incidencePrunedHost K D T).Adj := by
  unfold incidencePrunedHost
  infer_instance

theorem incidencePrunedHost_le {W : Type*} [Fintype W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (D T : ℕ) : incidencePrunedHost K D T ≤ K :=
  (show incidencePrunedHost K D T ≤ degreePrunedGraph K D from inf_le_left).trans
    (degreePrunedGraph_le K D)

theorem incidencePrunedHost_degree_le {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (D T : ℕ) (x : W) :
    (incidencePrunedHost K D T).degree x ≤ D := by
  have hle : incidencePrunedHost K D T ≤ degreePrunedGraph K D := inf_le_left
  exact ((SimpleGraph.Copy.ofLE _ _ hle).degree_le x).trans (degreePrunedGraph_degree_le K D x)

theorem incidencePrunedHost_induced_density {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (D T : ℕ) (S : Finset W) :
    ((incidencePrunedHost K D T).induce (S : Set W)).edgeSet.ncard ≤ T * S.card := by
  have hle : incidencePrunedHost K D T ≤ lowEndpointPrunedGraph K T := inf_le_right
  have hInduce : (incidencePrunedHost K D T).induce (S : Set W) ≤
      (lowEndpointPrunedGraph K T).induce (S : Set W) := fun _ _ h => hle h
  exact (copy_edge_ncard_le (SimpleGraph.Copy.ofLE _ _ hInduce)).trans
    (lowEndpointPrunedGraph_induced_density K T S)

theorem incidencePrunedHost_cross_degree {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (D T : ℕ) (x : W)
    (hx : x ∉ highHostVertices K T) :
    (highLowGraph (incidencePrunedHost K D T) (highHostVertices K T)).degree x ≤ T :=
  highLowGraph_low_degree _ K (incidencePrunedHost_le K D T) T x hx

theorem incidencePrunedHost_copy_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph W) [DecidableRel K.Adj]
    (right : Finset V) (d Δ D T : ℕ) (M : ℝ)
    (hcover : G.IsVertexCover (right : Set V)) (hdegree : ∀ v ∈ right, G.degree v ≤ d)
    (hmax : ∀ v, G.degree v ≤ Δ)
    (hbudget : (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard)
    (hcutoff : 16 * M * d * Δ ≤ (D : ℝ))
    (hright : 32 * (M * d) * d ≤ ((T + 1 : ℕ) : ℝ)) (f : G.Copy K) :
    ((copyRawEdges f ∩ (K \ incidencePrunedHost K D T).edgeFinset).card : ℝ) ≤
      (3 / 16 : ℝ) * G.edgeSet.ncard := by
  classical
  have hbudget' : (K.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hbudget
  have hglobal := near_regular_initial_pruning_capacity G K d Δ D M hmax hbudget hcutoff f
  have hlocal := incidence_high_high_pruning_budget G K f right d T (M * d)
    hcover hdegree hbudget' hright
  have hsum : ((copyRawEdges f ∩ (K \ incidencePrunedHost K D T).edgeFinset).card : ℝ) ≤
      (copyRawEdges f ∩ (K \ degreePrunedGraph K D).edgeFinset).card +
        (copyRawEdges f ∩ (K \ lowEndpointPrunedGraph K T).edgeFinset).card := by
    have hsub : (K \ incidencePrunedHost K D T).edgeFinset ⊆
        (K \ degreePrunedGraph K D).edgeFinset ∪ (K \ lowEndpointPrunedGraph K T).edgeFinset := by
      intro e he
      have heSet := (K \ incidencePrunedHost K D T).mem_edgeFinset.mp he
      rw [incidencePrunedHost, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_inf] at heSet
      simp only [Set.mem_sdiff, Set.mem_inter_iff] at heSet
      simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff,
        Set.mem_sdiff]
      tauto
    have hNat := (Finset.card_le_card (Finset.inter_subset_inter_left (s := copyRawEdges f) hsub)).trans
      (copy_capacity_union_inter (copyRawEdges f) (K \ degreePrunedGraph K D).edgeFinset
        (K \ lowEndpointPrunedGraph K T).edgeFinset)
    exact_mod_cast hNat
  linarith only [hsum, hglobal, hlocal]

theorem incidence_initial_pruning_capacity {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : SimpleGraph W) [DecidableRel K.Adj]
    (right : Finset V) (d Δ : ℕ) (M : ℝ)
    (hcover : G.IsVertexCover (right : Set V)) (hdegree : ∀ v ∈ right, G.degree v ≤ d)
    (hmax : ∀ v, G.degree v ≤ Δ)
    (hbudget : (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard) (f : G.Copy K) :
    ((copyRawEdges f ∩
      (K \ incidencePrunedHost K (nearRegularHostCutoff M d Δ) (incidenceRightCutoff M d)).edgeFinset).card : ℝ) ≤
        (3 / 16 : ℝ) * G.edgeSet.ncard := by
  have hcutoff : 16 * M * d * Δ ≤ (nearRegularHostCutoff M d Δ : ℝ) := Nat.le_ceil _
  have hright : 32 * (M * d) * d ≤ ((incidenceRightCutoff M d + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil (32 * M * d * d)
    change 32 * M * d * d ≤ (incidenceRightCutoff M d : ℝ) at h
    push_cast
    nlinarith only [h]
  exact incidencePrunedHost_copy_capacity G K right d Δ _ _ M hcover hdegree hmax hbudget hcutoff hright f

end Erdos911
