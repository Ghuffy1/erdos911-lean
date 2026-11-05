import Erdos911.RepeatedLabels
import Erdos911.InducedHostEdges

namespace Erdos911

theorem label_pair_eq_of_unique_endpoint {V A : Type*} (G : SimpleGraph V) (f : V → A)
    (hloc : ∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w)
    (S : Finset V) (u v x y : V) (hu : u ∈ S) (_hv : v ∈ S) (hx : x ∈ S) (hy : y ∈ S)
    (huv : G.Adj u v) (hxy : G.Adj x y) (hunique : u ∉ repeatedVertices S f)
    (heq : s(f u, f v) = s(f x, f y)) : s(u, v) = s(x, y) := by
  have huniq (w : V) (hw : w ∈ S) (he : f w = f u) : w = u := by
    by_contra hne
    exact hunique ((mem_repeatedVertices S f u).mpr ⟨hu, w, hw, hne, he⟩)
  rcases Sym2.eq_iff.mp heq with h | h
  · have hxu : x = u := huniq x hx h.1.symm
    subst x
    have hvy : v = y := hloc u v y huv hxy h.2
    subst y
    rfl
  · have hyu : y = u := huniq y hy h.1.symm
    subst y
    have hvx : v = x := hloc u v x huv hxy.symm h.2
    subst x
    exact Sym2.eq_swap

noncomputable def distinctLabelEdges {V A : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (f : V → A) : Finset (Sym2 V) :=
  inducedHostEdges G S \ inducedHostEdges G (repeatedVertices S f)

theorem mem_distinctLabelEdges {V A : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (f : V → A) (u v : V) :
    s(u, v) ∈ distinctLabelEdges G S f ↔
      G.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ ¬(u ∈ repeatedVertices S f ∧ v ∈ repeatedVertices S f) := by
  classical
  simp only [distinctLabelEdges, inducedHostEdges, Finset.mem_sdiff, Finset.mem_filter,
    SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, Finset.insert_subset_iff,
    Finset.singleton_subset_iff]
  tauto

theorem distinctLabelEdges_injOn {V A : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (f : V → A)
    (hloc : ∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w) :
    Set.InjOn (Sym2.map f) (distinctLabelEdges G S f : Set (Sym2 V)) := by
  intro e he e' he' hlabels
  induction e using Sym2.inductionOn with
  | _ u v =>
    induction e' using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨huv, hu, hv, hnot⟩ := (mem_distinctLabelEdges G S f u v).mp he
      obtain ⟨hxy, hx, hy, _⟩ := (mem_distinctLabelEdges G S f x y).mp he'
      change s(f u, f v) = s(f x, f y) at hlabels
      rcases not_and_or.mp hnot with huniqu | huniqv
      · exact label_pair_eq_of_unique_endpoint G f hloc S u v x y hu hv hx hy huv hxy huniqu hlabels
      · have hlabels' : s(f v, f u) = s(f x, f y) := Sym2.eq_swap.trans hlabels
        exact Sym2.eq_swap.trans (label_pair_eq_of_unique_endpoint G f hloc S v u x y
          hv hu hx hy huv.symm hxy huniqv hlabels')

theorem distinctLabelEdges_image_card {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (f : V → A)
    (hloc : ∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w) :
    ((distinctLabelEdges G S f).image (Sym2.map f)).card = (distinctLabelEdges G S f).card :=
  Finset.card_image_of_injOn (distinctLabelEdges_injOn G S f hloc)

/-- Removing edges between repeated-label vertices is enough to make
all remaining unordered label pairs distinct. Local density bounds the loss. -/
theorem distinct_label_pairs_density_bound {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (f : V → A)
    (hloc : ∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w)
    (σ : ℝ)
    (hsparse : ((G.induce (repeatedVertices S f : Set V)).edgeSet.ncard : ℝ) ≤
      σ * (repeatedVertices S f).card) :
    ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤
      ((distinctLabelEdges G S f).image (Sym2.map f)).card + σ * (repeatedVertices S f).card := by
  have hsub : inducedHostEdges G (repeatedVertices S f) ⊆ inducedHostEdges G S := by
    intro e he
    obtain ⟨heG, hend⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨heG, fun v hv => ((mem_repeatedVertices S f v).mp (hend hv)).1⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [← distinctLabelEdges, inducedHostEdges_card, inducedHostEdges_card] at hcard
  rw [distinctLabelEdges_image_card G S f hloc]
  have hcardR : ((distinctLabelEdges G S f).card : ℝ) +
      ((G.induce (repeatedVertices S f : Set V)).edgeSet.ncard : ℝ) =
      (G.induce (S : Set V)).edgeSet.ncard := by exact_mod_cast hcard
  linarith

end Erdos911
