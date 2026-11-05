import Erdos911.DenseBlockExtraction
import Erdos911.EdgeColorings
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Erdos911

noncomputable def copyVertexPreimage {V W : Type*} [Fintype V]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (S : Finset W) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => f v ∈ S)

theorem mem_copyVertexPreimage {V W : Type*} [Fintype V]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (S : Finset W) (v : V) :
    v ∈ copyVertexPreimage f S ↔ f v ∈ S := by
  classical
  simp only [copyVertexPreimage, Finset.mem_filter, Finset.mem_univ, true_and]

theorem copyVertexPreimage_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (S : Finset W) :
    (copyVertexPreimage f S).card ≤ S.card := by
  classical
  have himage : (copyVertexPreimage f S).image f ⊆ S := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact (mem_copyVertexPreimage f S v).mp hv
  calc
    (copyVertexPreimage f S).card = ((copyVertexPreimage f S).image f).card :=
      (Finset.card_image_of_injective _ f.injective).symm
    _ ≤ S.card := Finset.card_le_card himage

/-- Edges of a copy supported on a host vertex set come from the induced
target subgraph on the inverse image of that set. -/
theorem copyHostEdges_inter_subset_induce {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (S : Finset W)
    (E : Finset H.edgeSet)
    (hsupport : ∀ u v (h : H.Adj u v), (⟨s(u, v), h⟩ : H.edgeSet) ∈ E →
      u ∈ S ∧ v ∈ S) :
    copyHostEdges f ∩ E ⊆ copyHostEdges
      (f.comp (SimpleGraph.Copy.induce G (copyVertexPreimage f S : Set V))) := by
  classical
  intro e he
  obtain ⟨hecopy, heE⟩ := Finset.mem_inter.mp he
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hecopy
  obtain ⟨a, ha⟩ := a
  induction a using Sym2.inductionOn with
  | hf u v =>
    have huv : G.Adj u v := ha
    have hs := hsupport (f u) (f v) (map_rel f.toHom huv) heE
    have hu : u ∈ copyVertexPreimage f S := by
      simp only [copyVertexPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs.1
    have hv : v ∈ copyVertexPreimage f S := by
      simp only [copyVertexPreimage, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs.2
    let a' : (G.induce (copyVertexPreimage f S : Set V)).edgeSet :=
      ⟨s(⟨u, hu⟩, ⟨v, hv⟩), huv⟩
    apply Finset.mem_map.mpr
    refine ⟨a', Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    rfl

theorem copyHostEdges_supported_card_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (S : Finset W)
    (E : Finset H.edgeSet)
    (hsupport : ∀ u v (h : H.Adj u v), (⟨s(u, v), h⟩ : H.edgeSet) ∈ E →
      u ∈ S ∧ v ∈ S) :
    (copyHostEdges f ∩ E).card ≤
      (G.induce (copyVertexPreimage f S : Set V)).edgeSet.ncard := by
  classical
  have h := Finset.card_le_card (copyHostEdges_inter_subset_induce f S E hsupport)
  rw [copyHostEdges_card] at h
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using h

noncomputable def blockHostEdges {W : Type*} [Fintype W] (H : SimpleGraph W)
    (B : RectangleBlock W) : Finset H.edgeSet := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ B.edges)

theorem mem_blockHostEdges {W : Type*} [Fintype W] (H : SimpleGraph W)
    (B : RectangleBlock W) (e : H.edgeSet) : e ∈ blockHostEdges H B ↔ e.val ∈ B.edges := by
  classical
  simp only [blockHostEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Local sparsity bounds the edges of any target copy used by one block. -/
theorem block_copy_capacity_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : G.Copy H)
    (q : ℕ) (ρ σ : ℝ) (hσ : 0 ≤ σ) (B : RectangleBlock W) (hB : B.Valid H q ρ)
    (hlocal : ∀ U : Finset V, U.card ≤ 2 * q →
      ((G.induce (U : Set V)).edgeSet.ncard : ℝ) ≤ σ * U.card) :
    ((copyHostEdges f ∩ blockHostEdges H B).card : ℝ) ≤ 2 * σ * q := by
  classical
  let S := B.left ∪ B.right
  have hsource : ∀ u v (h : H.Adj u v), (⟨s(u, v), h⟩ : H.edgeSet) ∈ blockHostEdges H B →
      u ∈ S ∧ v ∈ S := by
    intro u v h he
    have hmem : s(u, v) ∈ B.edges := (mem_blockHostEdges H B ⟨s(u, v), h⟩).mp he
    exact rectangleEdges_endpoints H B.left B.right (hB.2.2.2.1 hmem)
  have hcard : (copyVertexPreimage f S).card ≤ 2 * q := by
    exact (copyVertexPreimage_card_le f S).trans_eq hB.support_card
  have hle : ((copyHostEdges f ∩ blockHostEdges H B).card : ℝ) ≤
      (G.induce (copyVertexPreimage f S : Set V)).edgeSet.ncard := by
    exact_mod_cast copyHostEdges_supported_card_le f S (blockHostEdges H B) hsource
  calc
    ((copyHostEdges f ∩ blockHostEdges H B).card : ℝ) ≤
        (G.induce (copyVertexPreimage f S : Set V)).edgeSet.ncard := hle
    _ ≤ σ * (copyVertexPreimage f S).card := hlocal _ hcard
    _ ≤ σ * ((2 * q : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hσ
    _ = 2 * σ * q := by push_cast; ring

/-- Total block capacity in the dense-block extraction. Each target copy
uses at most `2 * sigma * q` edges per block. -/
theorem block_packing_copy_capacity_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (f : G.Copy H)
    (q : ℕ) (ρ σ : ℝ) (hq : 0 < q) (hρ : 0 < ρ) (hσ : 0 ≤ σ)
    (P : Finset (RectangleBlock W)) (hP : ValidBlockPacking H q ρ P)
    (hlocal : ∀ U : Finset V, U.card ≤ 2 * q →
      ((G.induce (U : Set V)).edgeSet.ncard : ℝ) ≤ σ * U.card) :
    (∑ B ∈ P, ((copyHostEdges f ∩ blockHostEdges H B).card : ℝ)) ≤
      2 * σ * H.edgeFinset.card / (ρ * q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hbound := validBlockPacking_capacity_bound H q ρ P hP (by positivity)
    (fun B => ((copyHostEdges f ∩ blockHostEdges H B).card : ℝ))
    (2 * σ * q) (by positivity) (fun B hB => block_copy_capacity_le G H f q ρ σ hσ B
      (hP.1 B hB) hlocal)
  calc
    (∑ B ∈ P, ((copyHostEdges f ∩ blockHostEdges H B).card : ℝ)) ≤
        (2 * σ * q) * H.edgeFinset.card / (ρ * q * q) := hbound
    _ = 2 * σ * H.edgeFinset.card / (ρ * q) := by
      field_simp

end Erdos911
