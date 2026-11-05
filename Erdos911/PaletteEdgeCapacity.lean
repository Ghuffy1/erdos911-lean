import Erdos911.DistinctLabelPairs
import Erdos911.PaletteCopies

namespace Erdos911

theorem palette_collision_edge_loss {V A : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) (c : V → A)
    (d k : ℕ) (σ : ℝ) (hk : 0 < k) (hσ : 0 ≤ σ)
    (hmin : ∀ v, d ≤ F.degree v)
    (hrep : k * (repeatedVertices S c).card ≤ 2 * S.card)
    (hsparse : ((F.induce (repeatedVertices S c : Set V)).edgeSet.ncard : ℝ) ≤
      σ * (repeatedVertices S c).card)
    (hmargin : 256 * σ ≤ (k : ℝ) * d) :
    ((F.induce (repeatedVertices S c : Set V)).edgeSet.ncard : ℝ) ≤
      (∑ v ∈ S, (F.degree v : ℝ)) / 128 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrepR : (repeatedVertices S c).card ≤ 2 * (S.card : ℝ) / k := by
    apply (le_div_iff₀ hkR).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using hrep)
  have hcoeff : 2 * σ / k ≤ (d : ℝ) / 128 := by
    apply (div_le_iff₀ hkR).mpr
    nlinarith only [hmargin]
  have hdegree : (d : ℝ) * S.card ≤ ∑ v ∈ S, (F.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ S, (d : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => by exact_mod_cast hmin v)
  calc
    _ ≤ σ * (repeatedVertices S c).card := hsparse
    _ ≤ σ * (2 * S.card / k) := mul_le_mul_of_nonneg_left hrepR hσ
    _ = (2 * σ / k) * S.card := by ring
    _ ≤ ((d : ℝ) / 128) * S.card := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)
    _ = ((d : ℝ) * S.card) / 128 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hdegree (by norm_num)

/-- A dense edge subset in a collision-controlled connected target set
contains many distinct unordered label pairs. This is the deterministic
input for both color tails in the bounded-component palette argument. -/
theorem dense_edge_set_has_many_label_pairs {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) (c : V → A)
    (E : Finset (Sym2 V)) (hE : E ⊆ inducedHostEdges F S)
    (hloc : ∀ u v w, F.Adj u v → F.Adj u w → c v = c w → v = w)
    (d k : ℕ) (σ : ℝ) (hk : 0 < k) (hσ : 0 ≤ σ)
    (hmin : ∀ v, d ≤ F.degree v)
    (hrep : k * (repeatedVertices S c).card ≤ 2 * S.card)
    (hsparse : ((F.induce (repeatedVertices S c : Set V)).edgeSet.ncard : ℝ) ≤
      σ * (repeatedVertices S c).card)
    (hmargin : 256 * σ ≤ (k : ℝ) * d)
    (hdense : (∑ v ∈ S, (F.degree v : ℝ)) ≤ 16 * E.card) :
    (∑ v ∈ S, (F.degree v : ℝ)) ≤ 32 * (E.image (Sym2.map c)).card := by
  classical
  let B := inducedHostEdges F (repeatedVertices S c)
  let T := E \ B
  have hT : T ⊆ distinctLabelEdges F S c := by
    intro e he
    exact Finset.mem_sdiff.mpr ⟨hE (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩
  have hinj : Set.InjOn (Sym2.map c) (T : Set (Sym2 V)) :=
    fun e he e' he' h => distinctLabelEdges_injOn F S c hloc (hT he) (hT he') h
  have hcard : (T.image (Sym2.map c)).card = T.card := Finset.card_image_of_injOn hinj
  have hsub : T.image (Sym2.map c) ⊆ E.image (Sym2.map c) :=
    Finset.image_subset_image Finset.sdiff_subset
  have hsmall : T.card ≤ (E.image (Sym2.map c)).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hsplit : E.card ≤ T.card + B.card := Finset.card_le_card_sdiff_add_card
  have hcount : (E.card : ℝ) ≤ (E.image (Sym2.map c)).card +
      (F.induce (repeatedVertices S c : Set V)).edgeSet.ncard := by
    have h := hsplit.trans (Nat.add_le_add_right hsmall B.card)
    rw [show B.card = (F.induce (repeatedVertices S c : Set V)).edgeSet.ncard from
      inducedHostEdges_card F _] at h
    exact_mod_cast h
  have hloss := palette_collision_edge_loss F S c d k σ hk hσ hmin hrep hsparse hmargin
  have himage : (0 : ℝ) ≤ (E.image (Sym2.map c)).card := Nat.cast_nonneg _
  nlinarith only [hcount, hloss, hdense, himage]

end Erdos911
