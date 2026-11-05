import Erdos911.PaletteFirstMoment
import Erdos911.PaletteBlueRetention
import Erdos911.PaletteBlueObstruction
import Erdos911.ComponentRetention

namespace Erdos911

/-- The complete deterministic/first-moment palette argument. All
numerical probability bounds and the initial host pruning capacity are
explicit inputs for the later quantitative parameter theorem. -/
theorem palette_avoiding_coloring_criterion {V U W A : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [Fintype W] [DecidableEq W]
    [Fintype A] [DecidableEq A]
    (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.ConnectedComponent]
    [∀ t : G.ConnectedComponent, Fintype t.supp]
    (F : SimpleGraph U) (K H : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (hHK : H ≤ K) (hFG : F.IsContained G) (hFedge : ∃ u v, F.Adj u v)
    (heG : 0 < G.edgeSet.ncard) (d L k : ℕ) (σ p q : ℝ)
    (hd : 0 < d) (hk : 0 < k) (hσ : 0 ≤ σ)
    (hmin : ∀ v, d ≤ G.degree v) (horder : ∀ t : G.ConnectedComponent, Fintype.card t.supp ≤ L)
    (hlocal : ∀ S : Finset V, S.card ≤ L → ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hmargin : 256 * σ ≤ (k : ℝ) * d)
    (c : W → A)
    (hloc : ∀ u v w, H.Adj u v → H.Adj u w → c v = c w → v = w)
    (hrep : ∀ S : Finset W, S.card ≤ L → (H.induce (S : Set W)).Connected →
      k * (repeatedVertices S c).card ≤ 2 * S.card)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hred : ∀ e : H.edgeSet, (bitProductMeasure (Sym2 A) p hp0 hp1).real
      {ω | e ∈ paletteRedSupport F H c ω} ≤ q)
    (hbad : ∀ t : G.ConnectedComponent, (bitProductMeasure (Sym2 A) p hp0 hp1).real
      (paletteComponentBad (G.induce t.supp) d) ≤ 1 / 1000)
    (hbudget : 64 * q * H.edgeSet.ncard + (4 / 1000 : ℝ) * G.edgeSet.ncard ≤ G.edgeSet.ncard)
    (hprune : ∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤
      (G.edgeSet.ncard : ℝ) / 64) :
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  obtain ⟨ω, hsupport, hbadmass⟩ := exists_palette_with_small_costs G F H c d p q hp0 hp1 hred hbad hbudget
  let S := paletteRedSupportRaw F H c ω
  let R := (paletteColorGraph H c ω false).deleteEdges (S : Set (Sym2 W))
  have hRH : R ≤ H := (SimpleGraph.deleteEdges_le _).trans (paletteColorGraph_le H c ω false)
  have hRK : R ≤ K := hRH.trans hHK
  have hredG : ¬G.IsContained R := fun h => (paletteRedSupportRaw_avoids F H c ω hFedge) (hFG.trans h)
  refine ⟨R, hRK, hredG, ?_⟩
  rintro ⟨g⟩
  let blue := paletteColorGraph H c ω true
  let J := copyRetainedGraph blue g
  have hJG : J ≤ G := copyRetainedGraph_le blue g
  let gK : G.Copy K := (SimpleGraph.Copy.ofLE _ _ sdiff_le).comp g
  have hraw : copyRawEdges gK = copyRawEdges g := copyRawEdges_ofLE_comp sdiff_le g
  have hpruned : ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 64 := by
    have h := hprune gK
    rwa [hraw] at h
  have hS : (S.card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 64 := by
    simpa only [S, paletteRedSupportRaw_card] using hsupport
  have hloss := palette_blue_copy_loss G K H c ω S g
  have hlossR : ((G \ J).edgeFinset.card : ℝ) ≤
      (copyRawEdges g ∩ (K \ H).edgeFinset).card + S.card := by exact_mod_cast hloss
  have hpartition := subgraph_edge_partition G J hJG
  have hpartitionR : ((G \ J).edgeFinset.card : ℝ) + J.edgeSet.ncard = G.edgeSet.ncard := by
    rw [J.edgeFinset_card, G.edgeFinset_card, Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard] at hpartition
    exact_mod_cast hpartition
  have hkeep : (7 / 8 : ℝ) * G.edgeSet.ncard ≤ J.edgeSet.ncard := by
    nlinarith only [hlossR, hpartitionR, hpruned, hS, Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard]
  let bad (t : G.ConnectedComponent) := ω ∈ paletteComponentBad (G.induce t.supp) d
  obtain ⟨t, htgood, htkeep⟩ := exists_good_retained_component G J hJG bad heG hkeep hbadmass
  let Gt := G.induce t.supp
  let Jt := J.induce t.supp
  have hJtGt : Jt ≤ Gt := fun _ _ h => hJG h
  have hminGt (v : t.supp) : d ≤ Gt.degree v := by
    rw [← Gt.ncard_neighborSet, component_neighbor_ncard_eq, G.ncard_neighborSet]
    exact hmin v.val
  have heGt : 0 < Gt.edgeSet.ncard := by
    obtain ⟨v, hv⟩ := t.nonempty_supp
    have hpos : 0 < Gt.degree ⟨v, hv⟩ := hd.trans_le (hminGt ⟨v, hv⟩)
    have h := hpos.trans_le (Gt.degree_le_card_edgeFinset ⟨v, hv⟩)
    simpa only [Gt.edgeFinset_card, Set.fintypeCard_eq_ncard] using h
  let gJ : J.Copy blue := retainedGraphCopy blue g
  let gH : J.Copy H := (SimpleGraph.Copy.ofLE _ _ (paletteColorGraph_le H c ω true)).comp gJ
  let gt : Jt.Copy H := gH.comp (SimpleGraph.Copy.induce J t.supp)
  have hlocalGt := induced_density_of_copy (SimpleGraph.Copy.induce G t.supp) L σ hlocal
  have hblue : ∀ u v, Jt.Adj u v → ω s(c (gt u), c (gt v)) = true := by
    intro u v huv
    exact ((paletteColorGraph_adj H c ω true (gJ u.val) (gJ v.val)).mp (map_rel gJ.toHom huv)).2
  have hBad := palette_bad_of_retained_blue_mass Gt Jt H hJtGt gt c ω d L k σ hd hk hσ
    (horder t) hminGt heGt htkeep hloc hrep hlocalGt hmargin hblue
  exact htgood hBad

end Erdos911
