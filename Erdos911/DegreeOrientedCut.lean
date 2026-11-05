import Erdos911.BinaryPatterns
import Erdos911.BipartiteComponents

namespace Erdos911

def orderedCutGraph {V : Type*} (G : SimpleGraph V) (w : V → ℕ) (ω : V → Bool) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧
    ((ω u = true ∧ ω v = false ∧ w v ≤ w u) ∨ (ω v = true ∧ ω u = false ∧ w u ≤ w v))
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := G.irrefl h.1

instance {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ) (ω : V → Bool) :
    DecidableRel (orderedCutGraph G w ω).Adj := by
  unfold orderedCutGraph
  infer_instance

theorem orderedCutGraph_le {V : Type*} (G : SimpleGraph V) (w : V → ℕ) (ω : V → Bool) :
    orderedCutGraph G w ω ≤ G := fun _ _ h => h.1

/-- A random bipartition preserves one quarter of any prescribed
weight-oriented edges. Equal endpoint weights cause no loss. -/
theorem exists_ordered_bipartite_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℕ) :
    ∃ (F : SimpleGraph V) (left right : Finset V), F ≤ G ∧
      F.IsBipartiteWith (left : Set V) (right : Set V) ∧ left ∪ right = Finset.univ ∧
      (G.edgeSet.ncard : ℝ) / 4 ≤ F.edgeSet.ncard ∧
      ∀ u ∈ left, ∀ v ∈ right, F.Adj u v → w v ≤ w u := by
  classical
  let tail : G.edgeSet → V := fun e =>
    if w e.val.out.2 ≤ w e.val.out.1 then e.val.out.1 else e.val.out.2
  let head : G.edgeSet → V := fun e =>
    if w e.val.out.2 ≤ w e.val.out.1 then e.val.out.2 else e.val.out.1
  have hadj (e : G.edgeSet) : G.Adj e.val.out.1 e.val.out.2 := by
    change s(e.val.out.1, e.val.out.2) ∈ G.edgeSet
    rw [show s(e.val.out.1, e.val.out.2) = e.val from e.val.out_eq]
    exact e.property
  have hpair (e : G.edgeSet) : s(tail e, head e) = e.val := by
    dsimp only [tail, head]
    split_ifs with h
    · exact e.val.out_eq
    · exact Sym2.eq_swap.trans e.val.out_eq
  have hne (e : G.edgeSet) : tail e ≠ head e := by
    have h := (hadj e).ne
    dsimp only [tail, head]
    split_ifs
    · exact h
    · exact h.symm
  have hweight (e : G.edgeSet) : w (head e) ≤ w (tail e) := by
    dsimp only [tail, head]
    split_ifs with h
    · exact h
    · exact Nat.le_of_not_ge h
  have htailadj (e : G.edgeSet) : G.Adj (tail e) (head e) := by
    dsimp only [tail, head]
    split_ifs
    · exact hadj e
    · exact (hadj e).symm
  obtain ⟨ω, S, hS, hmass⟩ := exists_many_binary_events (E := V) (I := G.edgeSet)
    (1 / 2) (1 / 4) (by norm_num) (by norm_num)
    (fun e => {ω | ω (tail e) = true ∧ ω (head e) = false}) (by
      intro e
      rw [bitProductMeasure_two_bits (tail e) (head e) (hne e) true false])
  let F := orderedCutGraph G w ω
  let left := Finset.univ.filter (fun v => ω v = true)
  let right := Finset.univ.filter (fun v => ω v = false)
  have hleft (v : V) : v ∈ left ↔ ω v = true := by simp only [left, Finset.mem_filter, Finset.mem_univ, true_and]
  have hright (v : V) : v ∈ right ↔ ω v = false := by simp only [right, Finset.mem_filter, Finset.mem_univ, true_and]
  have hBip : F.IsBipartiteWith (left : Set V) (right : Set V) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro v hvL hvR
      have ht := (hleft v).mp hvL
      have hf := (hright v).mp hvR
      simp only [ht, Bool.true_eq_false] at hf
    · intro u v huv
      rcases huv.2 with h | h
      · exact Or.inl ⟨(hleft u).mpr h.1, (hright v).mpr h.2.1⟩
      · exact Or.inr ⟨(hright u).mpr h.2.1, (hleft v).mpr h.1⟩
  have hsub : S.image Subtype.val ⊆ F.edgeFinset := by
    intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    have hω := (hS z).mp hz
    rw [← hpair z]
    exact F.mem_edgeFinset.mpr ⟨htailadj z, Or.inl ⟨hω.1, hω.2, hweight z⟩⟩
  have hcard : S.card ≤ F.edgeSet.ncard := by
    rw [← Finset.card_image_of_injective S Subtype.val_injective]
    exact (Finset.card_le_card hsub).trans_eq (by rw [F.edgeFinset_card, Set.fintypeCard_eq_ncard])
  have hmass' : (G.edgeSet.ncard : ℝ) / 4 ≤ S.card := by
    simpa only [Set.fintypeCard_eq_ncard, one_div, div_eq_mul_inv, mul_comm, one_mul] using hmass
  refine ⟨F, left, right, orderedCutGraph_le G w ω, hBip, ?_,
    hmass'.trans (by exact_mod_cast hcard), ?_⟩
  · ext v
    simp only [Finset.mem_union, hleft, hright, Finset.mem_univ, iff_true]
    cases ω v <;> simp
  · intro u hu v hv huv
    rcases huv.2 with h | h
    · exact h.2.2
    · have ht := (hleft u).mp hu
      simp only [ht, Bool.true_eq_false, false_and] at h
      exact h.2.elim

theorem exists_degree_oriented_bipartite_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (F : SimpleGraph V) (left right : Finset V), F ≤ G ∧
      F.IsBipartiteWith (left : Set V) (right : Set V) ∧ left ∪ right = Finset.univ ∧
      (G.edgeSet.ncard : ℝ) / 4 ≤ F.edgeSet.ncard ∧
      ∀ u ∈ left, ∀ v ∈ right, F.Adj u v → G.degree v ≤ G.degree u :=
  exists_ordered_bipartite_subgraph G (fun v => G.degree v)

end Erdos911
