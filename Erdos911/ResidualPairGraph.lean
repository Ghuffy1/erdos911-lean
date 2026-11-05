import Erdos911.ResidualCodegrees
import Erdos911.CopyImages

namespace Erdos911

noncomputable def highCodegreeGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : ℝ) : SimpleGraph V := by
  classical
  exact {
    Adj x y := x ≠ y ∧ T < ((neighbors G x ∩ neighbors G y).card : ℝ)
    symm.symm := by
      intro x y h
      exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩
    loopless.irrefl := by intro x h; exact h.1 rfl
  }

theorem highCodegreeGraph_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : ℝ) (x y : V) :
    (highCodegreeGraph G T).Adj x y ↔
      x ≠ y ∧ T < ((neighbors G x ∩ neighbors G y).card : ℝ) := Iff.rfl

/-- The degree estimate needs only the original degree bound at the
vertex being tested. This allows the other side of an incidence graph to
have a larger degree bound. -/
theorem highCodegreeGraph_degree_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : ℕ) (D T ρ : ℝ)
    [DecidableRel (highCodegreeGraph G T).Adj]
    (hq : 0 < q) (hρ : 0 ≤ ρ) (hT : 2 * (q : ℝ) ≤ T) (hgap : ρ * D < T - q)
    (hnodense : ∀ A B : Finset V, A.card = q → B.card = q → Disjoint A B →
      (crossEdges G A B : ℝ) ≤ ρ * q * q)
    (x : V) (hD : ((neighbors G x).card : ℝ) ≤ D) :
    (highCodegreeGraph G T).degree x < q := by
  classical
  have heq : (highCodegreeGraph G T).neighborFinset x =
      Finset.univ.filter (fun y => x ≠ y ∧
        T < ((neighbors G x ∩ neighbors G y).card : ℝ)) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, highCodegreeGraph_adj,
      Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, heq]
  exact residual_codegrees_at G q D T ρ hq hρ hT hgap hnodense x hD

theorem induced_highCodegreeGraph_degree_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Finset V) (q : ℕ) (D T ρ : ℝ)
    [DecidableRel (highCodegreeGraph G T).Adj]
    (hq : 0 < q) (hρ : 0 ≤ ρ) (hT : 2 * (q : ℝ) ≤ T) (hgap : ρ * D < T - q)
    (hnodense : ∀ A B : Finset V, A.card = q → B.card = q → Disjoint A B →
      (crossEdges G A B : ℝ) ≤ ρ * q * q)
    (hD : ∀ x ∈ X, ((neighbors G x).card : ℝ) ≤ D) (x : X) :
    ((highCodegreeGraph G T).induce (X : Set V)).degree x < q := by
  classical
  have hle := (SimpleGraph.Copy.induce (highCodegreeGraph G T) (X : Set V)).degree_le x
  exact hle.trans_lt (highCodegreeGraph_degree_lt G q D T ρ hq hρ hT hgap hnodense x.val
    (hD x.val x.property))

end Erdos911
