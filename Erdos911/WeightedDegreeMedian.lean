import Erdos911.BipartiteRestriction
import Mathlib.Data.Nat.Find

namespace Erdos911

/-- A positive integer-weight median splits the total weight in both
directions. Its value is attained, so lower bounds on positive weights
also hold for the chosen median. -/
theorem exists_weighted_degree_median {V : Type*} [DecidableEq V]
    (S : Finset V) (w : V → ℕ) (hpos : 0 < ∑ v ∈ S, w v) :
    ∃ p : ℕ, 0 < p ∧ (∃ v ∈ S, w v = p) ∧
      (∑ v ∈ S, w v) ≤ 2 * ∑ v ∈ S.filter (fun v => w v ≤ p), w v ∧
      (∑ v ∈ S, w v) ≤ 2 * ∑ v ∈ S.filter (fun v => p ≤ w v), w v := by
  classical
  let Q := fun p : ℕ => (∑ v ∈ S, w v) ≤ 2 * ∑ v ∈ S.filter (fun v => w v ≤ p), w v
  have hex : ∃ p, Q p := by
    refine ⟨S.sup w, ?_⟩
    have hfilter : S.filter (fun v => w v ≤ S.sup w) = S := by
      exact Finset.filter_eq_self.mpr (fun v hv => Finset.le_sup hv)
    dsimp only [Q]
    rw [hfilter]
    omega
  let p := Nat.find hex
  have hlo : Q p := Nat.find_spec hex
  have hp : 0 < p := by
    by_contra h
    have hz : p = 0 := by omega
    have hsum : ∑ v ∈ S.filter (fun v => w v ≤ p), w v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hle := (Finset.mem_filter.mp hv).2
      omega
    dsimp only [Q] at hlo
    rw [hsum] at hlo
    omega
  have hstrict : 2 * ∑ v ∈ S.filter (fun v => w v ≤ p - 1), w v < ∑ v ∈ S, w v := by
    have hnot := Nat.find_min hex (show p - 1 < p by omega)
    change ¬ Q (p - 1) at hnot
    dsimp only [Q] at hnot
    omega
  have hwitness : ∃ v ∈ S, w v = p := by
    by_contra hnone
    have heq : S.filter (fun v => w v ≤ p) = S.filter (fun v => w v ≤ p - 1) := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hv, hle⟩
        have hne : w v ≠ p := fun h => hnone ⟨v, hv, h⟩
        exact ⟨hv, by omega⟩
      · rintro ⟨hv, hle⟩
        exact ⟨hv, by omega⟩
    dsimp only [Q] at hlo
    rw [heq] at hlo
    omega
  have hsplit : (∑ v ∈ S.filter (fun v => w v ≤ p - 1), w v) +
      (∑ v ∈ S.filter (fun v => p ≤ w v), w v) = ∑ v ∈ S, w v := by
    have h := Finset.sum_filter_add_sum_filter_not S (fun v => w v ≤ p - 1) w
    have heq : S.filter (fun v => ¬ w v ≤ p - 1) = S.filter (fun v => p ≤ w v) := by
      apply Finset.ext
      intro v
      simp only [Finset.mem_filter]
      have hiff : (¬ w v ≤ p - 1) ↔ p ≤ w v := by omega
      exact and_congr_right (fun _ => hiff)
    simpa only [heq] using h
  refine ⟨p, hp, hwitness, hlo, ?_⟩
  omega

/-- The degree-weighted median of a bipartite left side has at least half
the original edges incident with either its lower or its upper part. -/
theorem exists_bipartite_degree_median {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (he : 0 < G.edgeSet.ncard) :
    ∃ p : ℕ, 0 < p ∧ (∃ v ∈ left, G.degree v = p) ∧
      G.edgeSet.ncard ≤ 2 * (G.between ((left.filter (fun v => G.degree v ≤ p)) : Set V)
        (right : Set V)).edgeSet.ncard ∧
      G.edgeSet.ncard ≤ 2 * (G.between ((left.filter (fun v => p ≤ G.degree v)) : Set V)
        (right : Set V)).edgeSet.ncard := by
  classical
  have htotal : ∑ v ∈ left, G.degree v = G.edgeSet.ncard := by
    have h := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hB
    simpa only [G.edgeFinset_card, Set.fintypeCard_eq_ncard] using h
  obtain ⟨p, hp, hv, hlo, hhi⟩ := exists_weighted_degree_median left (fun v => G.degree v)
    (by simpa only [htotal] using he)
  refine ⟨p, hp, hv, ?_, ?_⟩
  · rw [leftRestriction_edge_count G left right _ hB (Finset.filter_subset _ _)]
    simpa only [htotal] using hlo
  · rw [leftRestriction_edge_count G left right _ hB (Finset.filter_subset _ _)]
    simpa only [htotal] using hhi

end Erdos911
