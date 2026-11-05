import Erdos911.RetainedLabelCapacity
import Erdos911.BlueComponentProbability
import Erdos911.WeightedDenseSet

namespace Erdos911

/-- A component with three quarters of its edges retained in the original
blue palette supplies one of the forbidden blue label-map witnesses. -/
theorem palette_bad_of_retained_blue_mass {V W A : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [DecidableEq A]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hRF : R ≤ F) (f : R.Copy H)
    (c : W → A) (ω : Sym2 A → Bool) (d K k : ℕ) (σ : ℝ)
    (_hd : 0 < d) (hk : 0 < k) (hσ : 0 ≤ σ) (hcard : Fintype.card V ≤ K)
    (hmin : ∀ v, d ≤ F.degree v) (heF : 0 < F.edgeSet.ncard)
    (hkeep : (3 / 4 : ℝ) * F.edgeSet.ncard ≤ R.edgeSet.ncard)
    (hloc : ∀ u v w, H.Adj u v → H.Adj u w → c v = c w → v = w)
    (hrep : ∀ S : Finset W, S.card ≤ K → (H.induce (S : Set W)).Connected →
      k * (repeatedVertices S c).card ≤ 2 * S.card)
    (hlocal : ∀ S : Finset V, S.card ≤ K →
      ((F.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hmargin : 256 * σ ≤ (k : ℝ) * d)
    (hblue : ∀ u v, R.Adj u v → ω s(c (f u), c (f v)) = true) :
    ω ∈ paletteComponentBad F d := by
  classical
  have hsum : (∑ v, (F.degree v : ℝ)) = 2 * F.edgeSet.ncard := by
    have h := F.sum_degrees_eq_twice_card_edges
    rw [F.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
    exact_mod_cast h
  have he : (0 : ℝ) < F.edgeSet.ncard := by exact_mod_cast heF
  obtain ⟨U, hU, hconnR, hweight⟩ := exists_weighted_dense_connected_set R
    (fun v => (F.degree v : ℝ)) (fun v => Nat.cast_nonneg _) (by rw [hsum]; linarith)
  have hconnF : (F.induce (U : Set V)).Connected := hconnR.mono (fun _ _ h => hRF h)
  have hUK : U.card ≤ K := (Finset.card_le_univ U).trans hcard
  have horder := relative_degree_dense_set_order F R d hmin U hU hweight
  have hUbad : U ∈ paletteBadSets F d := (mem_paletteBadSets F d U).mpr
    ⟨Finset.card_pos.mpr hU, hconnF, by exact_mod_cast (show (d : ℝ) ≤ 4 * U.card by linarith)⟩
  let labels : V → A := c ∘ f
  have hlabels := palette_collision_bound_for_copy f c K k hrep U hUK hconnR
  have hlocR := locally_injective_palette_for_copy f c hloc
  have hrepeatCard : (repeatedVertices U labels).card ≤ K :=
    (Finset.card_le_card (fun v hv => ((mem_repeatedVertices U labels v).mp hv).1)).trans hUK
  have hlocalR := hlocal (repeatedVertices U labels) hrepeatCard
  let E := inducedHostEdges R U
  have hmass : (∑ v ∈ U, (F.degree v : ℝ)) ≤ 16 * E.card := by
    rw [show E.card = (R.induce (U : Set V)).edgeSet.ncard from inducedHostEdges_card R U]
    have heR : (0 : ℝ) ≤ (R.induce (U : Set V)).edgeSet.ncard := Nat.cast_nonneg _
    linarith
  have hpair := dense_retained_edges_have_many_label_pairs F R hRF U labels E le_rfl hlocR
    d k σ hk hσ hmin hlabels hlocalR hmargin hmass
  let g : ↥U → A := fun v => labels v.val
  have hsub : E.image (Sym2.map labels) ⊆ markedElements (inducedLabelPairs F U g) ω := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    induction a using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨haR, haU⟩ := Finset.mem_filter.mp ha
      have huv : R.Adj u v := R.mem_edgeFinset.mp haR
      have hu : u ∈ U := haU (by simp)
      have hv : v ∈ U := haU (by simp)
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_image.mpr
        exact ⟨s(⟨u, hu⟩, ⟨v, hv⟩), (F.induce (U : Set V)).mem_edgeFinset.mpr (hRF huv), rfl⟩
      · exact hblue u v huv
  have hmarked := Finset.card_le_card hsub
  have hmarkedR : ((E.image (Sym2.map labels)).card : ℝ) ≤
      (markedElements (inducedLabelPairs F U g) ω).card := by exact_mod_cast hmarked
  apply (mem_paletteComponentBad F d ω).mpr
  refine ⟨U, hUbad, g, ?_⟩
  change Nat.ceil ((degreeVolume F U : ℝ) / 32) ≤ _
  apply Nat.ceil_le.mpr
  rw [degreeVolume_real]
  nlinarith only [hpair, hmarkedR]

end Erdos911
