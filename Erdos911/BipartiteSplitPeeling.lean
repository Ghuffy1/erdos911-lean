import Erdos911.BipartiteRestriction

namespace Erdos911

/-- Splitting the left vertices and peeling both pieces preserves a
fixed fraction of the edges, including the two charges at right vertices. -/
theorem exists_bipartite_split_peeling {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right A : Finset V)
    (hBip : G.IsBipartiteWith (left : Set V) (right : Set V)) (hA : A ⊆ left) (q : ℕ)
    (hmin : ∀ v, v ∈ G.support → (q : ℝ) / 128 ≤ G.degree v) :
    ∃ J₀ J₁ : SimpleGraph V,
      J₀ ≤ G.between (A : Set V) (right : Set V) ∧
      J₁ ≤ G.between ((left \ A : Finset V) : Set V) (right : Set V) ∧
      (∀ v, v ∈ left → v ∈ J₀.support → (G.degree v : ℝ) / 8 ≤ (J₀.neighborSet v).ncard) ∧
      (∀ v, v ∈ left → v ∈ J₁.support → (G.degree v : ℝ) / 8 ≤ (J₁.neighborSet v).ncard) ∧
      (∀ v, v ∈ right → v ∈ J₀.support → (q : ℝ) / 65536 ≤ (J₀.neighborSet v).ncard) ∧
      (∀ v, v ∈ right → v ∈ J₁.support → (q : ℝ) / 65536 ≤ (J₁.neighborSet v).ncard) ∧
      (3 / 4 : ℝ) * G.edgeSet.ncard ≤ (J₀.edgeSet.ncard : ℝ) + J₁.edgeSet.ncard := by
  classical
  let B := left \ A
  let H₀ := G.between (A : Set V) (right : Set V)
  let H₁ := G.between (B : Set V) (right : Set V)
  let t₀ := fun v => if v ∈ A then (G.degree v : ℝ) / 8 else (q : ℝ) / 65536
  let t₁ := fun v => if v ∈ B then (G.degree v : ℝ) / 8 else (q : ℝ) / 65536
  have ht₀ : ∀ v, 0 ≤ t₀ v := by intro v; dsimp only [t₀]; split_ifs <;> positivity
  have ht₁ : ∀ v, 0 ≤ t₁ v := by intro v; dsimp only [t₁]; split_ifs <;> positivity
  have hB : B ⊆ left := Finset.sdiff_subset
  have hBi₀ := leftRestriction_bipartite G left right A hBip hA
  have hBi₁ := leftRestriction_bipartite G left right B hBip hB
  have hH₀ : H₀ ≤ G := G.between_le
  have hH₁ : H₁ ≤ G := G.between_le
  obtain ⟨J₀, hJ₀, hm₀, he₀⟩ := exists_degree_peeling H₀ t₀ ht₀
  obtain ⟨J₁, hJ₁, hm₁, he₁⟩ := exists_degree_peeling H₁ t₁ ht₁
  have hc₀ := supportWeight_bipartite_bound H₀ G hH₀ A right hBi₀
    (fun v => (G.degree v : ℝ) / 8) ((q : ℝ) / 65536) (by intro v; positivity) (by positivity)
  have hc₁ := supportWeight_bipartite_bound H₁ G hH₁ B right hBi₁
    (fun v => (G.degree v : ℝ) / 8) ((q : ℝ) / 65536) (by intro v; positivity) (by positivity)
  have hr := active_right_size_bound G left right hBip ((q : ℝ) / 128) hmin
  have hpartition : (∑ v ∈ A, (G.degree v : ℝ) / 8) +
      (∑ v ∈ B, (G.degree v : ℝ) / 8) = (G.edgeSet.ncard : ℝ) / 8 := by
    rw [← Finset.sum_div, ← Finset.sum_div, ← add_div]
    have hs := Finset.sum_sdiff hA (f := fun v => (G.degree v : ℝ))
    have he := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hBip
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at he
    have heR : (∑ v ∈ left, (G.degree v : ℝ)) = G.edgeSet.ncard := by exact_mod_cast he
    dsimp only [B]
    rw [add_comm, hs, heR]
  have hepartition := left_partition_edge_counts G left right A hBip hA
  have hepartitionR : (H₀.edgeSet.ncard : ℝ) + H₁.edgeSet.ncard = G.edgeSet.ncard := by
    exact_mod_cast hepartition
  rw [H₀.edgeFinset_card, Set.fintypeCard_eq_ncard] at he₀
  rw [H₁.edgeFinset_card, Set.fintypeCard_eq_ncard] at he₁
  have htotal : (3 / 4 : ℝ) * G.edgeSet.ncard ≤ (J₀.edgeSet.ncard : ℝ) + J₁.edgeSet.ncard := by
    have hGpos : (0 : ℝ) ≤ G.edgeSet.ncard := Nat.cast_nonneg _
    change supportWeight H₀ t₀ ≤ _ at hc₀
    change supportWeight H₁ t₁ ≤ _ at hc₁
    nlinarith only [he₀, he₁, hc₀, hc₁, hr, hpartition, hepartitionR, hGpos]
  have hleftMem (S : Finset V) (hS : S ⊆ left) (v : V) (hv : v ∈ left)
      (hs : v ∈ (G.between (S : Set V) (right : Set V)).support) : v ∈ S := by
    obtain ⟨u, hvu⟩ := hs
    rcases (leftRestriction_bipartite G left right S hBip hS).mem_of_adj hvu with h | h
    · exact h.1
    · exact (Set.disjoint_left.mp hBip.disjoint hv h.1).elim
  have hnotMem (S : Finset V) (hS : S ⊆ left) (v : V) (hv : v ∈ right) : v ∉ S := by
    intro hs
    exact Set.disjoint_left.mp hBip.disjoint (hS hs) hv
  refine ⟨J₀, J₁, hJ₀, hJ₁, ?_, ?_, ?_, ?_, htotal⟩
  · intro v hv hs
    have hvA := hleftMem A hA v hv (J₀.support_mono hJ₀ hs)
    simpa only [t₀, ite_eq_left hvA] using hm₀ v hs
  · intro v hv hs
    have hvB := hleftMem B hB v hv (J₁.support_mono hJ₁ hs)
    simpa only [t₁, ite_eq_left hvB] using hm₁ v hs
  · intro v hv hs
    simpa only [t₀, ite_eq_right (hnotMem A hA v hv)] using hm₀ v hs
  · intro v hv hs
    simpa only [t₁, ite_eq_right (hnotMem B hB v hv)] using hm₁ v hs

end Erdos911
