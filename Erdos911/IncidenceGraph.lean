import Erdos911.NeighborhoodNormalization
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Erdos911

def incidenceGraph {L R : Type*} [DecidableEq L] (N : R → Finset L) :
    SimpleGraph (L ⊕ R) where
  Adj
    | .inl x, .inr y => x ∈ N y
    | .inr y, .inl x => x ∈ N y
    | _, _ => False
  symm.symm a b h := by cases a <;> cases b <;> exact h
  loopless.irrefl a := by cases a <;> exact not_false

instance {L R : Type*} [DecidableEq L] (N : R → Finset L) :
    DecidableRel (incidenceGraph N).Adj := by
  intro a b
  cases a <;> cases b <;> unfold incidenceGraph <;> infer_instance

theorem incidenceGraph_mono {L R : Type*} [DecidableEq L] {N S : R → Finset L}
    (hS : ∀ y, S y ⊆ N y) : incidenceGraph S ≤ incidenceGraph N := by
  intro a b h
  cases a <;> cases b
  · exact h.elim
  · exact hS _ h
  · exact hS _ h
  · exact h.elim

theorem incidenceGraph_neighbor_left {L R : Type*} [DecidableEq L] [Fintype L]
    [DecidableEq R] [Fintype R] (N : R → Finset L) (x : L) :
    (incidenceGraph N).neighborFinset (.inl x) =
      (Finset.univ.filter (fun y => x ∈ N y)).map Function.Embedding.inr := by
  ext v
  rw [(incidenceGraph N).mem_neighborFinset (.inl x) v]
  cases v <;> simp [incidenceGraph]

theorem incidenceGraph_neighbor_right {L R : Type*} [DecidableEq L] [Fintype L]
    [DecidableEq R] [Fintype R] (N : R → Finset L) (y : R) :
    (incidenceGraph N).neighborFinset (.inr y) =
      (N y).map Function.Embedding.inl := by
  ext v
  rw [(incidenceGraph N).mem_neighborFinset (.inr y) v]
  cases v <;> simp [incidenceGraph]

theorem incidenceGraph_degree_left {L R : Type*} [DecidableEq L] [Fintype L]
    [DecidableEq R] [Fintype R] (N : R → Finset L) (x : L) :
    (incidenceGraph N).degree (.inl x) =
      (Finset.univ.filter (fun y => x ∈ N y)).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, incidenceGraph_neighbor_left]
  exact Finset.card_map _

theorem incidenceGraph_degree_right {L R : Type*} [DecidableEq L] [Fintype L]
    [DecidableEq R] [Fintype R] (N : R → Finset L) (y : R) :
    (incidenceGraph N).degree (.inr y) = (N y).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, incidenceGraph_neighbor_right]
  exact Finset.card_map _

theorem incidenceGraph_bipartite {L R : Type*} [DecidableEq L] [Fintype L]
    [DecidableEq R] [Fintype R] (N : R → Finset L) :
    (incidenceGraph N).IsBipartiteWith
      (Finset.univ.map Function.Embedding.inl : Finset (L ⊕ R))
      (Finset.univ.map Function.Embedding.inr : Finset (L ⊕ R)) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro v hv hw
    cases v <;> simp_all
  · intro a b h
    cases a <;> cases b <;> simp_all [incidenceGraph]

theorem incidenceGraph_edge_count {L R : Type*} [DecidableEq L] [Fintype L]
    [DecidableEq R] [Fintype R] (N : R → Finset L) :
    (incidenceGraph N).edgeFinset.card = ∑ y, (N y).card := by
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
    (incidenceGraph_bipartite N)
  rw [Finset.sum_map] at h
  calc
    (incidenceGraph N).edgeFinset.card =
        ∑ y, (incidenceGraph N).degree (Function.Embedding.inr y) := h.symm
    _ = ∑ y, (N y).card := Finset.sum_congr rfl (fun y _ => incidenceGraph_degree_right N y)

/-- The neighborhood normalization gives an actual subgraph, with exact right
degree, controlled left degree, and the corresponding retained edge mass. -/
theorem exists_normalized_incidence_subgraph {m n : ℕ}
    (N : Fin n → Finset (Fin m)) (q a b r : ℕ)
    (hq : ∀ y, q ≤ (N y).card)
    (ha : ∀ x, (Finset.univ.filter (fun y => x ∈ N y)).card ≤ a)
    (hb : ∀ y, (N y).card ≤ b)
    (hr : ∀ x, r ≤ (Finset.univ.filter (fun y => x ∈ N y)).card)
    (hc : Real.exp 1 * Real.exp (-((q : ℝ) / b * r) / 8) * ((a * b : ℕ) + 1) ≤ 1) :
    ∃ S : Fin n → Finset (Fin m),
      incidenceGraph S ≤ incidenceGraph N ∧
        (∀ y, (incidenceGraph S).degree (.inr y) = q) ∧
          (∀ x, (q : ℝ) / b * r / 2 < (incidenceGraph S).degree (.inl x)) ∧
            (incidenceGraph S).edgeFinset.card = n * q ∧
              (q : ℝ) * (incidenceGraph N).edgeFinset.card ≤
                b * (incidenceGraph S).edgeFinset.card := by
  obtain ⟨S, hS, hleft⟩ := exists_degree_normalization N q a b r hq ha hb hr hc
  have hedge : (incidenceGraph S).edgeFinset.card = n * q := by
    rw [incidenceGraph_edge_count]
    simp only [(hS _).2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  refine ⟨S, incidenceGraph_mono (fun y => (hS y).1), ?_, ?_, hedge, ?_⟩
  · intro y
    rw [incidenceGraph_degree_right]
    exact (hS y).2
  · intro x
    simpa only [incidenceGraph_degree_left] using hleft x
  · have hcount : (incidenceGraph N).edgeFinset.card ≤ n * b := by
      rw [incidenceGraph_edge_count]
      calc
        (∑ y : Fin n, (N y).card) ≤ ∑ _y : Fin n, b :=
          Finset.sum_le_sum (fun y _ => hb y)
        _ = n * b := by simp
    have hcountR : ((incidenceGraph N).edgeFinset.card : ℝ) ≤ (n : ℝ) * b := by
      exact_mod_cast hcount
    rw [hedge]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcountR (Nat.cast_nonneg q)]

end Erdos911
