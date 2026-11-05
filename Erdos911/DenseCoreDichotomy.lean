import Erdos911.CorePackingGraph
import Erdos911.VertexDeletion

namespace Erdos911

set_option maxHeartbeats 400000 in

/-- Packing dense small cores either captures enough edges in bounded
components, or leaves a dense target with the requested local sparsity.
Both alternatives are actual copies of the original graph. -/
theorem dense_core_or_locally_sparse_target {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d Δ K s : ℕ)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ) :
    (∃ (U : Set V) (W : SimpleGraph U), W.IsContained G ∧
      (∀ v, s ≤ (W.neighborSet v).ncard) ∧
      (∀ c : W.ConnectedComponent, Nat.card c.supp ≤ K) ∧
      (s : ℝ) * G.edgeSet.ncard ≤ 8 * Δ * W.edgeSet.ncard) ∨
    (∃ (U : Set V) (F : SimpleGraph U), F.IsContained G ∧
      (∀ v, d / 4 ≤ (F.neighborSet v).ncard) ∧
      (∀ v, (F.neighborSet v).ncard ≤ Δ) ∧
      (∀ T : Finset U, T.card ≤ K →
        ((F.induce (T : Set U)).edgeSet.ncard : ℝ) ≤ (s : ℝ) * T.card) ∧
      (G.edgeSet.ncard : ℝ) / 4 ≤ F.edgeSet.ncard) := by
  classical
  obtain ⟨P, hP, hsparse⟩ := exists_dense_core_packing G K s
  let S := P.biUnion id
  by_cases hremoved : (G.edgeSet.ncard : ℝ) / 4 ≤ (Δ : ℝ) * S.card
  · left
    let J := corePackingGraph G P
    let W := J.induce (S : Set V)
    have hsupport : J.support ⊆ (S : Set V) := corePackingGraph_support G P
    have hsame : W.edgeSet.ncard = J.edgeSet.ncard := edge_ncard_induce_of_support_subset J _ hsupport
    have hcopy : W.IsContained G := ⟨(SimpleGraph.Copy.ofLE J G (corePackingGraph_le G P)).comp
      (SimpleGraph.Copy.induce J (S : Set V))⟩
    refine ⟨(S : Set V), W, hcopy, ?_, ?_, ?_⟩
    · intro v
      have hdeg : (W.neighborSet v).ncard = (J.neighborSet v.val).ncard := by
        simpa only [← SimpleGraph.ncard_neighborSet] using
          J.degree_induce_of_support_subset hsupport v
      have h := corePackingGraph_degree_lower G K s P hP v.val v.property
      rw [hdeg]
      simpa only [SimpleGraph.ncard_neighborSet] using h
    · exact corePackingGraph_component_order G K s P hP
    · have hmass := corePackingGraph_edge_mass G K s P hP
      rw [hsame]
      have h₁ := mul_le_mul_of_nonneg_left hremoved (Nat.cast_nonneg (α := ℝ) s)
      have h₂ := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg (α := ℝ) Δ)
      change (s : ℝ) * S.card ≤ 2 * J.edgeSet.ncard at hmass
      nlinarith only [h₁, h₂]
  · right
    let H := G.induce (S : Set V)ᶜ
    have hcost := vertex_deletion_edge_cost G S Δ hmax
    have hremain : 3 * (G.edgeSet.ncard : ℝ) / 4 ≤ H.edgeSet.ncard := by
      have hcostR : (G.edgeSet.ncard : ℝ) ≤ H.edgeSet.ncard + (Δ : ℝ) * S.card := by
        exact_mod_cast (by simpa only [Nat.mul_comm] using hcost)
      linarith only [hcostR, lt_of_not_ge hremoved]
    have hn : (d : ℝ) * Fintype.card V ≤ 2 * G.edgeSet.ncard := by
      have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hmin v)
      have hs := G.sum_degrees_eq_twice_card_edges
      rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hs
      have hnat : d * Fintype.card V ≤ 2 * G.edgeSet.ncard := by simpa [hs, mul_comm] using hsum
      exact_mod_cast hnat
    have hHcard : Fintype.card ↥(S : Set V)ᶜ ≤ Fintype.card V :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    obtain ⟨U, F, hFH, hFmin, hFmass⟩ := exists_min_degree_subgraph H ((d : ℝ) / 4) (by positivity)
    obtain ⟨f⟩ := hFH
    let g := (SimpleGraph.Copy.induce G (S : Set V)ᶜ).comp f
    let U' : Set V := Set.range g
    let e : U ≃ U' := Equiv.ofInjective g g.injective
    let F' : SimpleGraph U' := F.map e
    let iso : F ≃g F' := SimpleGraph.Iso.map e F
    have f' : F'.Copy G := g.comp iso.symm.toCopy
    have hlocalH := complement_induced_local_density G S K (s : ℝ) hsparse
    have hlocalF := induced_density_of_copy f K (s : ℝ) hlocalH
    have hlocalF' := induced_density_of_copy iso.symm.toCopy K (s : ℝ) hlocalF
    have hcount : F'.edgeSet.ncard = F.edgeSet.ncard := by
      simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using iso.card_edgeFinset_eq.symm
    refine ⟨U', F', ⟨f'⟩, ?_, ?_, hlocalF', ?_⟩
    · intro v
      have hdeg := iso.degree_eq (iso.symm v)
      have hmin' : d / 4 ≤ F.degree (iso.symm v) := by
        have hdFloor : ((d / 4 : ℕ) : ℝ) ≤ (d : ℝ) / 4 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
          exact_mod_cast Nat.div_mul_le_self d 4
        have h := hFmin (iso.symm v)
        rw [SimpleGraph.ncard_neighborSet] at h
        exact_mod_cast (hdFloor.trans h)
      have h := hmin'
      rw [← hdeg] at h
      have heq : iso (iso.symm v) = v := iso.apply_symm_apply v
      rw [heq] at h
      simpa only [SimpleGraph.ncard_neighborSet] using h
    · intro v
      have h := (f'.degree_le v).trans (hmax (f' v))
      simpa only [SimpleGraph.ncard_neighborSet] using h
    · rw [hcount]
      rw [H.edgeFinset_card, Set.fintypeCard_eq_ncard] at hFmass
      have hcardR : (Fintype.card ↥(S : Set V)ᶜ : ℝ) ≤ Fintype.card V := by exact_mod_cast hHcard
      have hmul := mul_le_mul_of_nonneg_left hcardR (show 0 ≤ (d : ℝ) / 4 by positivity)
      nlinarith only [hFmass, hremain, hn, hmul]

end Erdos911
