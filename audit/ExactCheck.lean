import Erdos911.FullProof

open Filter SimpleGraph

-- The acceptance target is written out, rather than relying only on an alias.
example :
    ∃ f : ℝ → ℝ, Tendsto (fun x ↦ f x / x) atTop atTop ∧
      ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
        C * n ≤ (G.edgeSet.ncard : ℝ) →
          f C * G.edgeSet.ncard < (sizeRamsey G G : ℝ) :=
  Erdos911.erdos_911_full_proof

#print axioms Erdos911.erdos_911_full_proof
#check Erdos911.erdos_911_full_proof
