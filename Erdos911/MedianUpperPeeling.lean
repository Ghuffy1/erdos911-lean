import Erdos911.MedianDegreeCover
import Erdos911.DegreeThresholdSplit

namespace Erdos911

/-- Peeling the upper-median side preserves a fixed fraction of all
edges while imposing left and right minimum degrees at their own scales. -/
theorem exists_median_upper_peeling {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (p : ℕ) (r : ℝ)
    (hr : 0 < r) (hrp : r ≤ p) (hmin : ∀ v, v ∈ G.support → r ≤ G.degree v)
    (hhalf : G.edgeSet.ncard ≤ 2 * (G.between
      ((left.filter (fun v => p ≤ G.degree v)) : Set V) (right : Set V)).edgeSet.ncard) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartiteWith (left : Set V) (right : Set V) ∧
      (∀ v ∈ left, v ∈ H.support → (p : ℝ) / 8 ≤ (H.neighborSet v).ncard) ∧
      (∀ v ∈ right, v ∈ H.support → r / 16 ≤ (H.neighborSet v).ncard) ∧
      (∀ v ∈ H.support, r / 16 ≤ (H.neighborSet v).ncard) ∧
      (5 / 16 : ℝ) * G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  let A := left.filter (fun v => p ≤ G.degree v)
  let F := G.between (A : Set V) (right : Set V)
  let t := fun v => if v ∈ A then (p : ℝ) / 8 else r / 16
  have hA : A ⊆ left := Finset.filter_subset _ _
  have hFB : F.IsBipartiteWith (A : Set V) (right : Set V) := leftRestriction_bipartite G left right A hB hA
  have hFG : F ≤ G := G.between_le
  have ht : ∀ v, 0 ≤ t v := by intro v; dsimp only [t]; split_ifs <;> positivity
  obtain ⟨H, hHF, hHmin, hmass⟩ := exists_degree_peeling F t ht
  have hHG : H ≤ G := hHF.trans hFG
  have hHB : H.IsBipartiteWith (left : Set V) (right : Set V) := bipartite_of_le H G hHG _ _ hB
  have hcost := supportWeight_bipartite_bound F G hFG A right hFB
    (fun _ => (p : ℝ) / 8) (r / 16) (by intro; positivity) (by positivity)
  have hAsize : (p : ℝ) * A.card ≤ G.edgeSet.ncard := by
    have h₁ : (p : ℝ) * A.card ≤ ∑ v ∈ A, (G.degree v : ℝ) := by
      calc
        _ = ∑ _v ∈ A, (p : ℝ) := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun v hv => by
          exact_mod_cast (Finset.mem_filter.mp hv).2)
    have h₂ : (∑ v ∈ A, (G.degree v : ℝ)) ≤ ∑ v ∈ left, (G.degree v : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun v _ _ => Nat.cast_nonneg _)
    have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hB
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
    have hsumR : (∑ v ∈ left, (G.degree v : ℝ)) = G.edgeSet.ncard := by exact_mod_cast hsum
    exact h₁.trans (h₂.trans_eq hsumR)
  have hRsize := active_right_size_bound G left right hB r hmin
  have hcost' : supportWeight F t ≤ (3 / 16 : ℝ) * G.edgeSet.ncard := by
    change supportWeight F t ≤ _ at hcost
    simp only [Finset.sum_const, nsmul_eq_mul] at hcost
    nlinarith only [hcost, hAsize, hRsize]
  have hhalfN : G.edgeSet.ncard ≤ 2 * F.edgeSet.ncard := by
    simpa only [F, A, Finset.coe_filter] using hhalf
  have hhalfR : (G.edgeSet.ncard : ℝ) ≤ 2 * F.edgeSet.ncard := by exact_mod_cast hhalfN
  rw [F.edgeFinset_card, Set.fintypeCard_eq_ncard] at hmass
  have hleft (v : V) (hv : v ∈ left) (hs : v ∈ H.support) :
      (p : ℝ) / 8 ≤ (H.neighborSet v).ncard := by
    obtain ⟨w, hvw⟩ := hs
    have hvA : v ∈ A := by
      rcases hFB.mem_of_adj (hHF hvw) with h | h
      · exact h.1
      · exact (Set.disjoint_left.mp hB.disjoint hv h.1).elim
    simpa only [t, ite_eq_left hvA] using hHmin v ⟨w, hvw⟩
  have hright (v : V) (hv : v ∈ right) (hs : v ∈ H.support) :
      r / 16 ≤ (H.neighborSet v).ncard := by
    have hvA : v ∉ A := fun h => Set.disjoint_left.mp hB.disjoint (hA h) hv
    simpa only [t, ite_eq_right hvA] using hHmin v hs
  refine ⟨H, hHG, hHB, hleft, hright, ?_, ?_⟩
  · intro v hs
    obtain ⟨w, hvw⟩ := hs
    rcases hHB.mem_of_adj hvw with h | h
    · have hdegree := hleft v h.1 ⟨w, hvw⟩
      linarith only [hdegree, hrp, hr]
    · exact hright v h.1 ⟨w, hvw⟩
  · nlinarith only [hmass, hcost', hhalfR]

end Erdos911
