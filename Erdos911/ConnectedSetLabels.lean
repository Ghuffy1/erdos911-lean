import Erdos911.GraphWalkBall
import Erdos911.DictionaryHostGraph

namespace Erdos911

theorem boundedWalkGraph_adj_of_connected_set {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℕ) (S : Finset V)
    (hsize : S.card ≤ a) (hconn : (G.induce (S : Set V)).Connected)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) :
    (boundedWalkGraph G a).Adj u v := by
  let uS : (S : Set V) := ⟨u, hu⟩
  let vS : (S : Set V) := ⟨v, hv⟩
  obtain ⟨p, hp⟩ := hconn.exists_isPath uS vS
  have hlen : p.length ≤ a := by
    have hh := hp.length_lt
    have hcard : Fintype.card (S : Set V) = S.card := by simp
    rw [hcard] at hh
    omega
  let inclusion := (SimpleGraph.Embedding.induce (G := G) (S : Set V)).toHom
  refine ⟨hne, (mem_graphWalkBall_iff G a u v).mpr ⟨p.map inclusion, ?_⟩⟩
  change (p.map inclusion).length ≤ a
  rw [SimpleGraph.Walk.length_map]
  exact hlen

/-- One coloring is injective on every connected vertex set of size at
most a, independently of how many such sets the graph contains. -/
theorem exists_connected_set_labels {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (a : ℕ) :
    ∃ c : V → Fin ((D + 1) ^ a + 1),
      ∀ S : Finset V, S.card ≤ a → (G.induce (S : Set V)).Connected → Set.InjOn c (S : Set V) := by
  classical
  obtain ⟨c, hc⟩ := exists_degree_coloring (boundedWalkGraph G a) ((D + 1) ^ a)
    (boundedWalkGraph_degree_le G D hD a)
  refine ⟨c, ?_⟩
  intro S hsize hconn u hu v hv hcolor
  by_contra hne
  exact hc u v (boundedWalkGraph_adj_of_connected_set G a S hsize hconn u v hu hv hne) hcolor

/-- The dictionary conflict graph has a host-order-independent label
set which is injective on every connected set of bounded size. -/
theorem exists_dictionary_host_labels {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (C : ℝ) (hC : 0 ≤ C) (a : ℕ) :
    ∃ c : V → Fin ((Nat.ceil (C * D) + 1) ^ a + 1),
      ∀ S : Finset V, S.card ≤ a →
        ((dictionaryHostGraph K D C).induce (S : Set V)).Connected → Set.InjOn c (S : Set V) := by
  classical
  exact exists_connected_set_labels (dictionaryHostGraph K D C) (Nat.ceil (C * D))
    (dictionaryHostGraph_degree_le_ceil K D C hC) a

end Erdos911
