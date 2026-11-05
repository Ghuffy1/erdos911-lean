import Erdos911.IncidenceClassColoring
import Erdos911.IncidenceHostParameters
import Erdos911.PolynomialTripleLogClass

namespace Erdos911

/-- The incidence branch has every fixed linear-in-right-degree Ramsey
multiplier, uniformly in graph order and without a host-degree assumption. -/
theorem incidence_size_ramsey_lower_bound (B : ℕ) (M C τ : ℝ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) (hτ : 0 < τ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) → (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      (∀ S : Finset (Fin n), S.card ≤ 2 * nearRegularBlockSize d →
        ((G.induce (S : Set (Fin n))).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      ∀ left right : Finset (Fin n), G.IsBipartiteWith (left : Set (Fin n)) (right : Set (Fin n)) →
      (∀ v ∈ right, (G.neighborSet v).ncard = d) →
      (∀ v ∈ left, (d : ℝ) * (Real.log d) ^ τ ≤ (G.neighborSet v).ncard) →
      (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨dR, hdR⟩ := incidence_class_coloring (B + 2) M C τ hM hC hτ
  obtain ⟨dD, hdD⟩ := incidence_host_parameters_uniform B M hM
  obtain ⟨dC, hdC⟩ := polynomial_triple_log_component_class B M C hM hC
  obtain ⟨dQ, hdQ⟩ := near_regular_block_sizes_ordered_uniform
  refine ⟨max 2 (max dR (max dD (max dC dQ))), ?_⟩
  intro d hd n G hn hmin hmax hlocal left right hBip hright hleft
  classical
  have hmin : ∀ v, d ≤ G.degree v := by simpa only [G.ncard_neighborSet] using hmin
  have hmax : ∀ v, G.degree v ≤ d ^ B := by simpa only [G.ncard_neighborSet] using hmax
  have hright : ∀ v ∈ right, G.degree v = d := by simpa only [G.ncard_neighborSet] using hright
  have hleft : ∀ v ∈ left, (d : ℝ) * (Real.log d) ^ τ ≤ G.degree v := by
    simpa only [G.ncard_neighborSet] using hleft
  let D := nearRegularHostCutoff M d (d ^ B)
  let P := incidenceRightCutoff M d
  obtain ⟨hdD, hDpow, hdeltaD, hPlo, hPhi⟩ := hdD d (by omega)
  have hGmax : ∀ v, G.degree v ≤ D := fun v => (hmax v).trans hdeltaD
  have hq := hdQ d (by omega)
  have hlocalSmall : ∀ S : Finset (Fin n), S.card ≤ 2 * baselineBlockSize d →
      ((G.induce (S : Set (Fin n))).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card := by
    intro S hS
    exact hlocal S (hS.trans (Nat.mul_le_mul_left 2 hq))
  by_contra hnot
  have hcheap : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * d) * G.edgeSet.ncard := le_of_not_gt hnot
  obtain ⟨t, hclass⟩ := hdC d (by omega) n G hn
    (by simpa only [G.ncard_neighborSet] using hmin)
    (by simpa only [G.ncard_neighborSet] using hmax) hlocalSmall hcheap
  obtain ⟨m, K, hKsize, hRamsey⟩ := sizeRamsey_attained G G
  have hKbudget : (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    simpa only [hKsize] using hcheap
  let H := incidencePrunedHost K D P
  have hH : H ≤ lowEndpointPrunedGraph K P := inf_le_right
  have hHdegree : ∀ w, H.degree w ≤ D := incidencePrunedHost_degree_le K D P
  have hinitial : ∀ f : G.Copy K,
      ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4 := by
    intro f
    have h := incidence_initial_pruning_capacity G K right d (d ^ B) M
      (bipartite_right_isVertexCover G left right hBip) (fun v hv => (hright v hv).le) hmax hKbudget f
    have he : (0 : ℝ) ≤ G.edgeSet.ncard := Nat.cast_nonneg _
    linarith only [h, he]
  have hclass' : ∃ k e : ℕ,
      Real.exp ((e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
        ((componentClass G k e).card : ℝ) := by
    refine ⟨componentOrder G t, componentSize G t, ?_⟩
    simpa only [mul_comm] using hclass.le
  obtain ⟨R, hRK, hred, hblue⟩ := hdR d (by omega) (Fin n) (Fin m) D P G K H
    hH hmin hGmax hdD hDpow hHdegree hPlo hPhi hKbudget hinitial hlocal left right hBip hright hleft hclass'
  exact (hRamsey R hRK).elim hred hblue

end Erdos911
