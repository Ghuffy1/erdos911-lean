import Erdos911.BiasedRedConditions
import Erdos911.ComponentModels

namespace Erdos911

/-- The finite low-entropy coloring criterion for an arbitrary target of
positive order and sufficiently large minimum degree. -/
theorem minimum_degree_entropy_coloring {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (d Δ D : ℕ) (hd : 4 ≤ d) (hD : 2 ≤ D)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (hhost : 0 < H.edgeFinset.card)
    (p η : ℝ) (hp₀ : 0 < p) (hp : p ≤ 1 / 2)
    (hscale : 16 * Real.log D ≤ p * d)
    (hprune : (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) ≤
      η * G.edgeSet.ncard)
    (hbudget : componentEntropyMass G +
      forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent)
        H.edgeFinset.card Δ +
      ((1 - η) * G.edgeSet.ncard) * (Real.log p + 2 * (1 / (d : ℝ))) < 0) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  let t := componentTypeOf G (G.connectedComponentMk v)
  let F := componentModel G t
  have hFG : F.IsContained G := ⟨SimpleGraph.Copy.induce G _⟩
  have hF : F.Connected := componentModel_connected G t
  have hFmin : ∀ u, d ≤ F.degree u := by
    intro u
    have h := (componentModel_degree_bounds G d Δ hmin hmax t u).1
    simpa only [SimpleGraph.ncard_neighborSet] using h
  have hconditions := minimum_degree_red_conditions F hF d D p hd hD hFmin hp₀.le hp hscale
  have hneighbors : ∀ u, ∃ w, G.Adj u w := by
    intro u
    apply (G.degree_pos_iff_exists_adj u).mp
    exact lt_of_lt_of_le (by omega) (hmin u)
  exact biased_degree_pruned_entropy_coloring G F H hFG hF Δ D hmax hhost
    hneighbors (by obtain ⟨w, hw⟩ := hneighbors v; exact ⟨v, w, hw⟩)
    p (1 / d) η hp₀ (by linarith) hconditions.1 hconditions.2.1
    hconditions.2.2.1 hconditions.2.2.2 hprune hbudget

/-- Every Ramsey host satisfying the degree-cutoff hypotheses forces the
target's actual component-type entropy above the biased-coloring threshold. -/
theorem ramsey_component_entropy_lower_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (d Δ D : ℕ) (hd : 4 ≤ d) (hD : 2 ≤ D)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (hhost : 0 < H.edgeFinset.card) (hRamsey : RamseyFor G G H)
    (p η : ℝ) (hp₀ : 0 < p) (hp : p ≤ 1 / 2)
    (hscale : 16 * Real.log D ≤ p * d)
    (hprune : (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) ≤
      η * G.edgeSet.ncard) :
    ((1 - η) * G.edgeSet.ncard) * (-Real.log p - 2 * (1 / (d : ℝ))) -
      forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent)
        H.edgeFinset.card Δ ≤ componentEntropyMass G := by
  by_contra h
  have hbudget : componentEntropyMass G +
      forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent)
        H.edgeFinset.card Δ +
      ((1 - η) * G.edgeSet.ncard) * (Real.log p + 2 * (1 / (d : ℝ))) < 0 := by
    push Not at h
    nlinarith
  obtain ⟨R, hR, hred, hblue⟩ := minimum_degree_entropy_coloring G H d Δ D hd hD
    hmin hmax hhost p η hp₀ hp hscale hprune hbudget
  exact (hRamsey R hR).elim hred hblue

end Erdos911
