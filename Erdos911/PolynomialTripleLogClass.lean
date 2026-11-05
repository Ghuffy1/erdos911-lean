import Erdos911.PolynomialTripleLogEntropy

namespace Erdos911

/-- A linear-size Ramsey host forces a component class with the
triple-log exponent, under the stated polynomial-degree and sparsity bounds. -/
theorem polynomial_triple_log_component_class (B : ℕ) (M C : ℝ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) →
      (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      (∀ S : Finset (Fin n), S.card ≤ 2 * baselineBlockSize d →
        ((G.induce (S : Set (Fin n))).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * d) * G.edgeSet.ncard →
      ∃ t : ComponentType G,
        Real.exp ((tripleLogEntropyThreshold d - 3 * Real.log 2) * componentSize G t) <
          ((componentClass G (componentOrder G t) (componentSize G t)).card : ℝ) := by
  obtain ⟨d₀, hd₀⟩ := polynomial_triple_log_entropy_bound B M C hM hC
  refine ⟨max d₀ 1, ?_⟩
  intro d hd n G hn hmin hmax hlocal hcheap
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hd₀' : d₀ ≤ d := (le_max_left _ _).trans hd
  have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
  have hmin1 : ∀ v, 1 ≤ G.degree v := by
    intro v
    simpa only [G.ncard_neighborSet] using hd1.trans (hmin v)
  have hentropy : (G.edgeSet.ncard : ℝ) * tripleLogEntropyThreshold d < componentEntropyMass G := by
    by_contra h
    exact (not_lt_of_ge hcheap) (hd₀ d hd₀' n G hn hmin hmax hlocal (le_of_not_gt h))
  apply exists_large_component_class G hmin1 (tripleLogEntropyThreshold d - 3 * Real.log 2)
  nlinarith only [hentropy]

end Erdos911
