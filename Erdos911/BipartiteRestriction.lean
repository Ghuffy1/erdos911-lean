import Erdos911.BipartiteComponents
import Erdos911.DegreePeeling

namespace Erdos911

theorem leftRestriction_bipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (left right A : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (hA : A ⊆ left) :
    (G.between (A : Set V) (right : Set V)).IsBipartiteWith (A : Set V) (right : Set V) := by
  apply G.between_isBipartiteWith
  apply Set.disjoint_left.mpr
  intro v hvA hvR
  exact Set.disjoint_left.mp hB.disjoint (hA hvA) hvR

theorem leftRestriction_degree_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right A : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (hA : A ⊆ left)
    (v : V) (hv : v ∈ A) : (G.between (A : Set V) (right : Set V)).degree v = G.degree v := by
  classical
  have hset : (G.between (A : Set V) (right : Set V)).neighborSet v = G.neighborSet v := by
    ext u
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, Or.inl ⟨hv, hB.mem_of_mem_adj (hA hv) h⟩⟩
  have hcard := congrArg Set.ncard hset
  simpa only [SimpleGraph.ncard_neighborSet] using hcard

theorem leftRestriction_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right A : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (hA : A ⊆ left) :
    (G.between (A : Set V) (right : Set V)).edgeSet.ncard = ∑ v ∈ A, G.degree v := by
  classical
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (leftRestriction_bipartite G left right A hB hA)
  rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro v hv
  exact leftRestriction_degree_eq G left right A hB hA v hv

theorem left_partition_edge_counts {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right A : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (hA : A ⊆ left) :
    (G.between (A : Set V) (right : Set V)).edgeSet.ncard +
      (G.between ((left \ A : Finset V) : Set V) (right : Set V)).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  rw [leftRestriction_edge_count G left right A hB hA,
    leftRestriction_edge_count G left right (left \ A) hB Finset.sdiff_subset]
  have h := Finset.sum_sdiff hA (f := fun v => G.degree v)
  have hG := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hB
  rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hG
  omega

noncomputable def activeSide {V : Type*} (G : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact S.filter (fun v => v ∈ G.support)

theorem mem_activeSide {V : Type*} (G : SimpleGraph V) (S : Finset V) (v : V) :
    v ∈ activeSide G S ↔ v ∈ S ∧ v ∈ G.support := by
  classical
  exact Finset.mem_filter

theorem supportWeight_bipartite_bound {V : Type*} [Fintype V] [DecidableEq V]
    (F G : SimpleGraph V) (hFG : F ≤ G) (left right : Finset V)
    (hB : F.IsBipartiteWith (left : Set V) (right : Set V)) (a : V → ℝ) (b : ℝ)
    (ha : ∀ v, 0 ≤ a v) (hb : 0 ≤ b) :
    supportWeight F (fun v => if v ∈ left then a v else b) ≤
      (∑ v ∈ left, a v) + b * (activeSide G right).card := by
  classical
  let S := (Set.toFinite F.support).toFinset
  let R := activeSide G right
  let t := fun v => if v ∈ left then a v else b
  have ht : ∀ v, 0 ≤ t v := by
    intro v
    dsimp only [t]
    split_ifs
    · exact ha v
    · exact hb
  have hsub : S ⊆ left ∪ R := by
    intro v hv
    have hvF : v ∈ F.support := by simpa only [S, Set.Finite.mem_toFinset] using hv
    obtain ⟨u, hvu⟩ := hvF
    rcases hB.mem_of_adj hvu with h | h
    · exact Finset.mem_union_left _ h.1
    · exact Finset.mem_union_right _ ((mem_activeSide G right v).mpr ⟨h.1, u, hFG hvu⟩)
  have hdisjoint : Disjoint left R := by
    apply Finset.disjoint_left.mpr
    intro v hvL hvR
    exact Set.disjoint_left.mp hB.disjoint hvL ((mem_activeSide G right v).mp hvR).1
  calc
    _ = ∑ v ∈ S, t v := rfl
    _ ≤ ∑ v ∈ left ∪ R, t v := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun v _ _ => ht v)
    _ = (∑ v ∈ left, t v) + ∑ v ∈ R, t v := Finset.sum_union hdisjoint
    _ = (∑ v ∈ left, a v) + ∑ _v ∈ R, b := by
      congr 1
      · apply Finset.sum_congr rfl
        intro v hv
        exact ite_eq_left hv
      · apply Finset.sum_congr rfl
        intro v hv
        exact ite_eq_right (fun hvL => Finset.disjoint_left.mp hdisjoint hvL hv)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem active_right_size_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (d : ℝ)
    (hmin : ∀ v, v ∈ G.support → d ≤ G.degree v) :
    d * (activeSide G right).card ≤ (G.edgeSet.ncard : ℝ) := by
  classical
  calc
    _ = ∑ _v ∈ activeSide G right, d := by simp [mul_comm]
    _ ≤ ∑ v ∈ activeSide G right, (G.degree v : ℝ) :=
      Finset.sum_le_sum (fun v hv => hmin v ((mem_activeSide G right v).mp hv).2)
    _ ≤ ∑ v ∈ right, (G.degree v : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      (fun v hv => ((mem_activeSide G right v).mp hv).1) (fun v _ _ => Nat.cast_nonneg _)
    _ = _ := by
      have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hB
      rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
      exact_mod_cast h

end Erdos911
