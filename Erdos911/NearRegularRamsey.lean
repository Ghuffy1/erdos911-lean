import Erdos911.NearRegularClassColoring
import Erdos911.NearRegularHostParameters
import Erdos911.PolynomialTripleLogClass

namespace Erdos911

/-- The near-regular branch gives every fixed linear-in-degree Ramsey
multiplier, uniformly in graph order and without a host-degree assumption. -/
theorem near_regular_size_ramsey_lower_bound (A M C : ℝ)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n Δ : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) → (∀ v, (G.neighborSet v).ncard ≤ Δ) →
      (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
      (∀ S : Finset (Fin n), S.card ≤ 2 * nearRegularBlockSize d →
        ((G.induce (S : Set (Fin n))).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨dR, hdR⟩ := near_regular_class_coloring_ambient A M C hA hM hC
  obtain ⟨dD, hdD⟩ := near_regular_host_parameters_uniform A M hM
  obtain ⟨dC, hdC⟩ := polynomial_triple_log_component_class 3 M C hM hC
  obtain ⟨dQ, hdQ⟩ := near_regular_block_sizes_ordered_uniform
  refine ⟨max 2 (max dR (max dD (max dC dQ))), ?_⟩
  intro d hd n Δ G hn hmin hmax hdegree hlocal
  classical
  have hmin : ∀ v, d ≤ G.degree v := by simpa only [G.ncard_neighborSet] using hmin
  have hmax : ∀ v, G.degree v ≤ Δ := by simpa only [G.ncard_neighborSet] using hmax
  have hd2 : 2 ≤ d := (le_max_left _ _).trans hd
  let v₀ : Fin n := ⟨0, hn⟩
  have hΔ : 1 ≤ Δ := (show 1 ≤ d by omega).trans ((hmin v₀).trans (hmax v₀))
  let D := nearRegularHostCutoff M d Δ
  obtain ⟨hdD, hlower, hupper, hDpow⟩ := hdD d (by omega) Δ hΔ hdegree
  have hMd : (1 : ℝ) ≤ M * d := one_le_mul_of_one_le_of_one_le hM (by exact_mod_cast (show 1 ≤ d by omega))
  have hfactor : (1 : ℝ) ≤ 16 * M * d := by nlinarith only [hMd]
  have hΔD : Δ ≤ D := by
    have h := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg (α := ℝ) Δ)
    have hreal : (Δ : ℝ) ≤ D := by nlinarith only [h, hlower]
    exact_mod_cast hreal
  have hmaxPow : ∀ v, G.degree v ≤ d ^ 3 := fun v => (hmax v).trans (hΔD.trans hDpow)
  have hq := hdQ d (by omega)
  have hlocalSmall : ∀ S : Finset (Fin n), S.card ≤ 2 * baselineBlockSize d →
      ((G.induce (S : Set (Fin n))).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card := by
    intro S hS
    exact hlocal S (hS.trans (Nat.mul_le_mul_left 2 hq))
  by_contra hnot
  have hcheap : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * d) * G.edgeSet.ncard := le_of_not_gt hnot
  obtain ⟨t, hclass⟩ := hdC d (by omega) n G hn
    (by simpa only [G.ncard_neighborSet] using hmin)
    (by simpa only [G.ncard_neighborSet] using hmaxPow) hlocalSmall hcheap
  obtain ⟨m, K, hKsize, hRamsey⟩ := sizeRamsey_attained G G
  have hKbudget : (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    simpa only [hKsize] using hcheap
  let H := degreePrunedGraph K D
  have hHK : H ≤ K := degreePrunedGraph_le K D
  have hHdegree : ∀ w, H.degree w ≤ D := degreePrunedGraph_degree_le K D
  have hinitial : ∀ f : G.Copy K,
      ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4 := by
    intro f
    have h := near_regular_initial_pruning_capacity G K d Δ D M hmax hKbudget hlower f
    have he : (0 : ℝ) ≤ G.edgeSet.ncard := Nat.cast_nonneg _
    linarith only [h, he]
  have hclass' : ∃ k a : ℕ,
      Real.exp ((a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
        ((componentClass G k a).card : ℝ) := by
    refine ⟨componentOrder G t, componentSize G t, ?_⟩
    simpa only [mul_comm] using hclass.le
  obtain ⟨R, hRK, hred, hblue⟩ := hdR d (by omega) (Fin n) (Fin m) D Δ G K H hHK hmin hmax
    hdegree hdD hDpow hHdegree hlower hupper hKbudget hinitial hlocal hclass'
  exact (hRamsey R hRK).elim hred hblue

end Erdos911
