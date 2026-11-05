import Erdos911.WalkCounting
import Erdos911.SpanningWalk
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fintype.Pi

namespace Erdos911

noncomputable def rootedConnectedSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun S => root ∈ S ∧ S.card = k ∧ (G.induce (S : Set V)).Connected)

/-- Encode a rooted connected vertex set by the support of a closed walk. -/
theorem rooted_connected_set_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (root : V) (k : ℕ) :
    (rootedConnectedSets G root k).card ≤ D ^ (2 * (k - 1)) := by
  classical
  let walks := G.finsetWalkLength (2 * (k - 1)) root root
  have hsubset : rootedConnectedSets G root k ⊆ walks.image (fun p => p.support.toFinset) := by
    intro S hS
    have h := (Finset.mem_filter.mp hS).2
    obtain ⟨hroot, hcard, hconn⟩ := h
    let rootS : (S : Set V) := ⟨root, hroot⟩
    obtain ⟨p, hlength, hsupport⟩ := exists_closed_spanning_walk
      (G.induce (S : Set V)) hconn rootS
    let f := (SimpleGraph.Embedding.induce (G := G) (S : Set V)).toHom
    let q : G.Walk root root := p.map f
    have hlengthq : q.length = 2 * (k - 1) := by
      have horder : Fintype.card (S : Set V) = S.card := by
        simp
      change (p.map f).length = 2 * (k - 1)
      rw [SimpleGraph.Walk.length_map]
      simpa only [horder, hcard] using hlength
    have hsupportq : q.support.toFinset = S := by
      have heq : q.support.toFinset = p.support.toFinset.image (fun v => v.val) := by
        change (p.map f).support.toFinset = _
        rw [SimpleGraph.Walk.support_map]
        ext v
        simp [f]
      rw [heq, hsupport]
      ext v
      simp
    exact Finset.mem_image.mpr ⟨q, G.mem_finsetWalkLength_iff.mpr hlengthq, hsupportq⟩
  calc
    (rootedConnectedSets G root k).card ≤ (walks.image (fun p => p.support.toFinset)).card :=
      Finset.card_le_card hsubset
    _ ≤ walks.card := Finset.card_image_le
    _ ≤ D ^ (2 * (k - 1)) := walk_count_le G D hD _ root root

/-- Two homomorphisms agreeing on a spanning walk agree on every vertex. -/
theorem hom_eq_of_spanning_walk {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {H : SimpleGraph W} {root : V}
    (p : G.Walk root root) (hspan : p.support.toFinset = Finset.univ)
    (f g : G →g H) (h : ∀ i, f (p.getVert i) = g (p.getVert i)) : f = g := by
  ext v
  have hv : v ∈ p.support := by
    apply List.mem_toFinset.mp
    rw [hspan]
    exact Finset.mem_univ _
  obtain ⟨i, hi, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
  simpa only [hi] using h i

theorem rooted_homomorphism_count {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hG : G.Connected)
    (D : ℕ) (hD : ∀ w, H.degree w ≤ D) (root : V) (image : W) :
    Fintype.card {f : G →g H // f root = image} ≤ D ^ (2 * (Fintype.card V - 1)) := by
  classical
  obtain ⟨p, hlength, hspan⟩ := exists_closed_spanning_walk G hG root
  let encode : {f : G →g H // f root = image} →
      {q : H.Walk image image // q.length = 2 * (Fintype.card V - 1)} := fun f =>
    ⟨(p.map f.val).copy f.property f.property, by simpa using hlength⟩
  have hinj : Function.Injective encode := by
    intro f g hfg
    apply Subtype.ext
    apply hom_eq_of_spanning_walk p hspan
    intro i
    have h := congrArg (fun q => q.val.getVert i) hfg
    simpa only [encode, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map] using h
  have hcard := Fintype.card_le_of_injective encode hinj
  have htarget : Fintype.card {q : H.Walk image image //
      q.length = 2 * (Fintype.card V - 1)} =
        (H.finsetWalkLength (2 * (Fintype.card V - 1)) image image).card :=
    H.card_set_walk_length_eq image image _
  rw [htarget] at hcard
  exact hcard.trans (walk_count_le H D hD _ image image)

theorem rooted_copy_count {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hG : G.Connected)
    (D : ℕ) (hD : ∀ w, H.degree w ≤ D) (root : V) (image : W) :
    Fintype.card {f : G.Copy H // f root = image} ≤ D ^ (2 * (Fintype.card V - 1)) := by
  classical
  let forget : {f : G.Copy H // f root = image} → {f : G →g H // f root = image} :=
    fun f => ⟨f.val.toHom, f.property⟩
  have hinj : Function.Injective forget := by
    intro f g h
    apply Subtype.ext
    apply SimpleGraph.Copy.ext
    intro v
    exact congrArg (fun f : G →g H => f v) (congrArg Subtype.val h)
  exact (Fintype.card_le_of_injective forget hinj).trans
    (rooted_homomorphism_count G H hG D hD root image)

noncomputable def rootedConnectedSetsAtMost {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (s : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun S => root ∈ S ∧ S.card ≤ s ∧ (G.induce (S : Set V)).Connected)

theorem rooted_connected_sets_at_most_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (hDpos : 1 ≤ D) (root : V) (s : ℕ) :
    (rootedConnectedSetsAtMost G root s).card ≤ (s + 1) * D ^ (2 * s) := by
  classical
  have hsubset : rootedConnectedSetsAtMost G root s ⊆
      (Finset.range (s + 1)).biUnion (rootedConnectedSets G root) := by
    intro S hS
    obtain ⟨hroot, hcard, hconn⟩ := (Finset.mem_filter.mp hS).2
    apply Finset.mem_biUnion.mpr
    refine ⟨S.card, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot, rfl, hconn⟩
  calc
    (rootedConnectedSetsAtMost G root s).card ≤
        ((Finset.range (s + 1)).biUnion (rootedConnectedSets G root)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ k ∈ Finset.range (s + 1), (rootedConnectedSets G root k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (s + 1), D ^ (2 * s) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (rooted_connected_set_count G D hD root k).trans
      exact pow_le_pow_right₀ hDpos (by have := Finset.mem_range.mp hk; omega)
    _ = (s + 1) * D ^ (2 * s) := by simp

end Erdos911
