import Erdos911.DenseWitnessBound
import Erdos911.ComponentStatistics

namespace Erdos911

theorem exists_dense_connected_component {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d : ℕ) (hk : 0 < Fintype.card V)
    (haverage : d * Fintype.card V ≤ 2 * F.edgeSet.ncard) :
    ∃ c : F.ConnectedComponent, d * Nat.card c.supp ≤ 2 * (F.induce c.supp).edgeSet.ncard := by
  classical
  let : Fintype F.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hk
  by_contra hnone
  push Not at hnone
  have hsum := Finset.sum_lt_sum (fun c (_ : c ∈ (Finset.univ : Finset F.ConnectedComponent)) =>
    (hnone c).le) ⟨F.connectedComponentMk v, Finset.mem_univ _, hnone _⟩
  rw [← Finset.mul_sum, ← Finset.mul_sum, component_edge_count_sum,
    component_vertex_count_sum] at hsum
  omega

theorem average_degree_le_max {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d D : ℕ) (hk : 0 < Fintype.card V)
    (haverage : d * Fintype.card V ≤ 2 * F.edgeFinset.card)
    (hmax : ∀ v, F.degree v ≤ D) : d ≤ D := by
  have hsum : 2 * F.edgeFinset.card ≤ D * Fintype.card V := by
    calc
      2 * F.edgeFinset.card = ∑ v, F.degree v := F.sum_degrees_eq_twice_card_edges.symm
      _ ≤ ∑ _ : V, D := Finset.sum_le_sum (fun v _ => hmax v)
      _ = D * Fintype.card V := by simp [mul_comm]
  nlinarith

/-- The dense-witness lower bound applies to every nonempty subgraph,
without a connectedness assumption on that subgraph. -/
theorem subgraph_average_size_lower_bound {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (G : SimpleGraph U) [DecidableRel G.Adj]
    (hFG : F.IsContained G) (d Δ : ℕ) (hd : 4 ≤ d) (hk : 0 < Fintype.card V)
    (haverage : d * Fintype.card V ≤ 2 * F.edgeSet.ncard)
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    denseWitnessMultiplier d Δ * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  classical
  obtain ⟨c, hc⟩ := exists_dense_connected_component F d hk haverage
  let : Fintype c.supp := Fintype.ofFinite _
  let K := F.induce c.supp
  have hK : K.Connected := c.connected_toSimpleGraph
  have hKG : K.IsContained G := (show K.IsContained F from ⟨SimpleGraph.Copy.induce F c.supp⟩).trans hFG
  have hkK : 0 < Fintype.card c.supp := Fintype.card_pos_iff.mpr hK.nonempty
  have havgK : d * Fintype.card c.supp ≤ 2 * K.edgeFinset.card := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card,
      Set.fintypeCard_eq_ncard, K] using hc
  have hmaxK : ∀ v, K.degree v ≤ Δ := fun v => (hKG.some.degree_le v).trans (hΔ _)
  have hdΔ := average_degree_le_max K d Δ hkK havgK hmaxK
  have hdk := average_degree_le_max K d (Fintype.card c.supp) hkK havgK
    (fun v => (K.degree_lt_card_verts v).le)
  exact dense_witness_size_lower_bound K G hK hKG d Δ hd hdΔ hdk havgK hΔ

/-- A small size-Ramsey multiplier bounds the density of every nonempty
subgraph of the target. -/
theorem hereditary_average_degree_bound {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (G : SimpleGraph U) [DecidableRel G.Adj]
    (hFG : F.IsContained G) (d Δ : ℕ) (hd : 4 ≤ d) (hk : 0 < Fintype.card V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (Λ : ℝ)
    (hΛ : Λ ≤ denseWitnessMultiplier d Δ)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ Λ * G.edgeSet.ncard) :
    2 * F.edgeSet.ncard < d * Fintype.card V := by
  by_contra h
  have hlower := subgraph_average_size_lower_bound F G hFG d Δ hd hk (by omega) hΔ
  have hupper := mul_le_mul_of_nonneg_right hΛ (Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard)
  linarith

end Erdos911
