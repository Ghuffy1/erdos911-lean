import Erdos911.HostObstruction
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.VertexCover

namespace Erdos911

def incidentEdgesAtSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  S.biUnion (fun v => G.incidenceFinset v)

theorem incidentEdgesAtSet_card_le_on {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (Δ : ℕ)
    (hΔ : ∀ v ∈ S, G.degree v ≤ Δ) :
    (incidentEdgesAtSet G S).card ≤ S.card * Δ := by
  calc
    (incidentEdgesAtSet G S).card ≤ ∑ v ∈ S, (G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ S, G.degree v := by simp
    _ ≤ ∑ _v ∈ S, Δ := Finset.sum_le_sum hΔ
    _ = S.card * Δ := by simp

theorem incidentEdgesAtSet_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    (incidentEdgesAtSet G S).card ≤ S.card * Δ :=
  incidentEdgesAtSet_card_le_on G S Δ (fun v _ => hΔ v)

theorem edgeFinset_subset_incidentEdgesAtSet {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hcover : G.IsVertexCover (S : Set V)) :
    G.edgeFinset ⊆ incidentEdgesAtSet G S := by
  intro e he
  refine Sym2.inductionOn e (fun a b => ?_) he
  intro hab
  have hadj : G.Adj a b := by simpa using hab
  rcases hcover hadj with ha | hb
  · apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    rw [G.incidenceFinset_eq_filter]
    simp [hab]
  · apply Finset.mem_biUnion.mpr
    refine ⟨b, hb, ?_⟩
    rw [G.incidenceFinset_eq_filter]
    simp [hab]

theorem edges_le_cover_card_mul_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (Δ : ℕ)
    (hcover : G.IsVertexCover (S : Set V)) (hΔ : ∀ v, G.degree v ≤ Δ) :
    G.edgeFinset.card ≤ S.card * Δ :=
  (Finset.card_le_card (edgeFinset_subset_incidentEdgesAtSet G S hcover)).trans
    (incidentEdgesAtSet_card_le G S Δ hΔ)

theorem edges_le_cover_card_mul_degree_on {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (Δ : ℕ)
    (hcover : G.IsVertexCover (S : Set V)) (hΔ : ∀ v ∈ S, G.degree v ≤ Δ) :
    G.edgeFinset.card ≤ S.card * Δ :=
  (Finset.card_le_card (edgeFinset_subset_incidentEdgesAtSet G S hcover)).trans
    (incidentEdgesAtSet_card_le_on G S Δ hΔ)

theorem high_degree_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    d * (Finset.univ.filter (fun v => d ≤ G.degree v)).card ≤ 2 * G.edgeFinset.card := by
  let S := Finset.univ.filter (fun v => d ≤ G.degree v)
  calc
    d * S.card = ∑ _v ∈ S, d := by simp [mul_comm]
    _ ≤ ∑ v ∈ S, G.degree v :=
      Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
    _ ≤ ∑ v, G.degree v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => Nat.zero_le _)
    _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges

theorem high_degree_card_bound_real {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : 0 < d) :
    ((Finset.univ.filter (fun v => d ≤ G.degree v)).card : ℝ) ≤
      2 * G.edgeFinset.card / d := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0 : ℝ) < d)).mpr
  have h := high_degree_card_bound G d
  exact_mod_cast (by simpa [mul_comm] using h)

end Erdos911
