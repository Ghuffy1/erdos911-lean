import Erdos911.CandidateRectangles
import Mathlib.Data.Finset.Prod

namespace Erdos911

noncomputable def rectanglePairs {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    Finset (V × V) := by
  classical
  exact (A.product B).filter (fun p => G.Adj p.1 p.2)

noncomputable def rectangleEdges {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    Finset (Sym2 V) := by
  classical
  exact (rectanglePairs G A B).image (fun p => s(p.1, p.2))

theorem mem_rectangleEdges {V : Type*} (G : SimpleGraph V) (A B : Finset V) (e : Sym2 V) :
    e ∈ rectangleEdges G A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b ∧ s(a, b) = e := by
  classical
  simp only [rectangleEdges, Finset.mem_image, rectanglePairs, Finset.mem_filter,
    Prod.exists]
  aesop

theorem rectangleEdges_subset_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    rectangleEdges G A B ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨a, _, b, _, hab, rfl⟩ := (mem_rectangleEdges G A B e).mp he
  simpa using hab

theorem rectangleEdges_mono {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    (A B : Finset V) : rectangleEdges G A B ⊆ rectangleEdges H A B := by
  intro e he
  obtain ⟨a, ha, b, hb, hab, he⟩ := (mem_rectangleEdges G A B e).mp he
  exact (mem_rectangleEdges H A B e).mpr ⟨a, ha, b, hb, h hab, he⟩

theorem crossEdges_mono {V : Type*} {G H : SimpleGraph V} (h : G ≤ H)
    (A B : Finset V) : crossEdges G A B ≤ crossEdges H A B := by
  classical
  unfold crossEdges
  apply Finset.sum_le_sum
  intro u _
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hv, hadj⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hv, h hadj⟩

theorem rectangleEdges_card {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) : (rectangleEdges G A B).card = crossEdges G A B := by
  classical
  have hinj : Set.InjOn (fun p : V × V => s(p.1, p.2)) (rectanglePairs G A B) := by
    rintro ⟨a, b⟩ hp ⟨c, d⟩ hq he
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hq).1
    rcases Sym2.eq_iff.mp he with h | h
    · exact Prod.ext h.1 h.2
    · apply False.elim
      apply (Finset.disjoint_left.mp hAB) ha
      exact h.1.symm ▸ hd
  rw [rectangleEdges, Finset.card_image_iff.mpr hinj]
  simp only [rectanglePairs, crossEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_product A B (fun p : V × V => if G.Adj p.1 p.2 then (1 : ℕ) else 0)

theorem rectangleEdges_card_le {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    (rectangleEdges G A B).card ≤ A.card * B.card := by
  classical
  calc
    (rectangleEdges G A B).card ≤ (rectanglePairs G A B).card := Finset.card_image_le
    _ ≤ (A.product B).card := Finset.card_filter_le _ _
    _ = A.card * B.card := Finset.card_product _ _

theorem rectangleEdges_endpoints {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) {u v : V}
    (h : s(u, v) ∈ rectangleEdges G A B) : u ∈ A ∪ B ∧ v ∈ A ∪ B := by
  obtain ⟨a, ha, b, hb, _, heq⟩ := (mem_rectangleEdges G A B s(u, v)).mp h
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨Finset.mem_union_left B ha, Finset.mem_union_right A hb⟩
  · exact ⟨Finset.mem_union_right A hb, Finset.mem_union_left B ha⟩

end Erdos911
