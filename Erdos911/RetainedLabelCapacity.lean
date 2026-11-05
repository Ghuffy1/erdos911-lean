import Erdos911.PaletteEdgeCapacity

namespace Erdos911

theorem edge_card_le_label_pairs_add_repeated {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V) (c : V → A)
    (E : Finset (Sym2 V)) (hE : E ⊆ inducedHostEdges R S)
    (hloc : ∀ u v w, R.Adj u v → R.Adj u w → c v = c w → v = w) :
    (E.card : ℝ) ≤ (E.image (Sym2.map c)).card +
      (R.induce (repeatedVertices S c : Set V)).edgeSet.ncard := by
  classical
  let B := inducedHostEdges R (repeatedVertices S c)
  let T := E \ B
  have hT : T ⊆ distinctLabelEdges R S c := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨hE (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩
  have hinj : Set.InjOn (Sym2.map c) (T : Set (Sym2 V)) :=
    fun e he e' he' h => distinctLabelEdges_injOn R S c hloc (hT he) (hT he') h
  have hcard : (T.image (Sym2.map c)).card = T.card := Finset.card_image_of_injOn hinj
  have hsmall : T.card ≤ (E.image (Sym2.map c)).card := by
    rw [← hcard]
    exact Finset.card_le_card (Finset.image_subset_image Finset.sdiff_subset)
  have hsplit : E.card ≤ T.card + B.card := Finset.card_le_card_sdiff_add_card
  have h := hsplit.trans (Nat.add_le_add_right hsmall B.card)
  rw [show B.card = (R.induce (repeatedVertices S c : Set V)).edgeSet.ncard from
    inducedHostEdges_card R _] at h
  exact_mod_cast h

/-- The local density and degree volume belong to the original target;
local injectivity is needed only on the retained graph. -/
theorem dense_retained_edges_have_many_label_pairs {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj] (hRF : R ≤ F)
    (S : Finset V) (c : V → A) (E : Finset (Sym2 V)) (hE : E ⊆ inducedHostEdges R S)
    (hloc : ∀ u v w, R.Adj u v → R.Adj u w → c v = c w → v = w)
    (d k : ℕ) (σ : ℝ) (hk : 0 < k) (hσ : 0 ≤ σ)
    (hmin : ∀ v, d ≤ F.degree v)
    (hrep : k * (repeatedVertices S c).card ≤ 2 * S.card)
    (hsparse : ((F.induce (repeatedVertices S c : Set V)).edgeSet.ncard : ℝ) ≤
      σ * (repeatedVertices S c).card)
    (hmargin : 256 * σ ≤ (k : ℝ) * d)
    (hdense : (∑ v ∈ S, (F.degree v : ℝ)) ≤ 16 * E.card) :
    (∑ v ∈ S, (F.degree v : ℝ)) ≤ 32 * (E.image (Sym2.map c)).card := by
  have hcount := edge_card_le_label_pairs_add_repeated R S c E hE hloc
  have hsub : (R.induce (repeatedVertices S c : Set V)).edgeSet.ncard ≤
      (F.induce (repeatedVertices S c : Set V)).edgeSet.ncard :=
    copy_edge_ncard_le (SimpleGraph.Copy.ofLE _ _ (fun _ _ h => hRF h))
  have hsubR : ((R.induce (repeatedVertices S c : Set V)).edgeSet.ncard : ℝ) ≤
      (F.induce (repeatedVertices S c : Set V)).edgeSet.ncard := by exact_mod_cast hsub
  have hloss := palette_collision_edge_loss F S c d k σ hk hσ hmin hrep hsparse hmargin
  have himage : (0 : ℝ) ≤ (E.image (Sym2.map c)).card := Nat.cast_nonneg _
  nlinarith only [hcount, hsubR, hloss, hdense, himage]

end Erdos911
