import Erdos911.PaletteColoringCriterion
import Erdos911.RedPaletteCapacity
import Erdos911.PaletteNumericBudget

namespace Erdos911

/-- The sparse bounded-component palette theorem with every numerical
condition exposed. The host is arbitrary; its degree cutoff is constructed
inside the proof, and both monochromatic-copy obstructions are verified. -/
theorem sparse_palette_size_ramsey_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d Δ L D k : ℕ) (Λ σ p ℓ : ℝ)
    (hV : 0 < Fintype.card V) (hd : 0 < d) (hΔ : 1 ≤ Δ) (hL : 0 < L)
    (hD : 1000 ≤ D) (hk : 2 ≤ k) (_hΛ : 1 ≤ Λ) (hΛD : Λ ≤ D)
    (hσ : 0 ≤ σ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hℓ : 0 ≤ ℓ)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (horder : ∀ t : G.ConnectedComponent, Nat.card t.supp ≤ L)
    (hlocal : ∀ S : Finset V, S.card ≤ L → ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hmargin : 256 * σ ≤ (k : ℝ) * d) (hcut : 128 * Λ * Δ ≤ (D : ℝ))
    (hscale : 256 * Real.log D ≤ p * d)
    (hbase : 16 * Real.exp 1 * p ≤ Real.exp (-ℓ))
    (hentropy : Real.log (Fintype.card (CollisionPalette D L k)) + 2 * Real.log Δ ≤ (d : ℝ) * ℓ / 64)
    (hlog : 128 * Real.log 2 ≤ (d : ℝ) * ℓ)
    (hcomponent : Real.log L + Real.log 1000 ≤ (d : ℝ) ^ 2 * ℓ / 512) :
    Λ * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let : ∀ t : G.ConnectedComponent, Fintype t.supp := fun _ => Fintype.ofFinite _
  let : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨v₀⟩ := ‹Nonempty V›
  have heG : 0 < G.edgeSet.ncard := by
    have hvpos : 0 < G.degree v₀ := hd.trans_le (hmin v₀)
    have h := hvpos.trans_le (G.degree_le_card_edgeFinset v₀)
    simpa only [G.edgeFinset_card, Set.fintypeCard_eq_ncard] using h
  let t₀ := G.connectedComponentMk v₀
  let F := G.induce t₀.supp
  have hcomponentMin (t : G.ConnectedComponent) (v : t.supp) : d ≤ (G.induce t.supp).degree v := by
    rw [← SimpleGraph.ncard_neighborSet, component_neighbor_ncard_eq, G.ncard_neighborSet]
    exact hmin v.val
  have hcomponentMax (t : G.ConnectedComponent) (v : t.supp) : (G.induce t.supp).degree v ≤ Δ := by
    rw [← SimpleGraph.ncard_neighborSet, component_neighbor_ncard_eq, G.ncard_neighborSet]
    exact hmax v.val
  have hcomponentCard (t : G.ConnectedComponent) : Fintype.card t.supp ≤ L := by
    simpa only [Nat.card_eq_fintype_card] using horder t
  have hFconnected : F.Connected := t₀.connected_toSimpleGraph
  have hFedge : ∃ u v, F.Adj u v := by
    let u : t₀.supp := ⟨v₀, rfl⟩
    have hp : 0 < F.degree u := hd.trans_le (hcomponentMin t₀ u)
    obtain ⟨v, hv⟩ := (F.degree_pos_iff_exists_adj u).mp hp
    exact ⟨u, v, hv⟩
  have hFaverage : (d : ℝ) * Fintype.card t₀.supp ≤ 16 * F.edgeSet.ncard := by
    have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset t₀.supp)) => hcomponentMin t₀ v)
    rw [F.sum_degrees_eq_twice_card_edges, F.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
    have hbase : d * Fintype.card t₀.supp ≤ 2 * F.edgeSet.ncard := by simpa [mul_comm] using hsum
    have hreal : (d : ℝ) * Fintype.card t₀.supp ≤ 2 * F.edgeSet.ncard := by exact_mod_cast hbase
    nlinarith only [hreal, Nat.cast_nonneg (α := ℝ) F.edgeSet.ncard]
  have hFlocal := induced_density_of_copy (SimpleGraph.Copy.induce G t₀.supp) L σ hlocal
  apply (sizeRamsey_real_gt_iff G G (Λ * G.edgeSet.ncard)).mpr
  intro n K hK
  let H := degreePrunedGraph K D
  have hHK : H ≤ K := degreePrunedGraph_le K D
  have hHmax : ∀ w, H.degree w ≤ D := degreePrunedGraph_degree_le K D
  let A := CollisionPalette D L k
  let : Nonempty A := ⟨(⟨0, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩, ⟨0, Nat.zero_lt_succ _⟩)⟩
  obtain ⟨c, _, hcloc, hcrep⟩ := exists_collision_safe_palette H D L k (by omega) hk hHmax
  have hred : ∀ e : H.edgeSet, (bitProductMeasure (Sym2 A) p hp0 hp1).real
      {ω | e ∈ paletteRedSupport F H c ω} ≤ 1 / (D : ℝ) ^ 2 := by
    intro e
    have hprob (f : F.Copy H) : (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteRedEvent f c) ≤
        Real.exp (-p * ((d : ℝ) * Fintype.card t₀.supp / 32)) := by
      apply paletteRedEvent_exp_bound f c p _ hp0 hp1
      have hpairs := red_pattern_distinct_pairs F H hFconnected f c d L k σ (by omega) hσ
        (hcomponentCard t₀) hcloc hcrep hFlocal hmargin hFaverage
      linarith only [hpairs]
    have h := paletteRedSupport_probability F H hFconnected D hHmax c p
      (Real.exp (-p * ((d : ℝ) * Fintype.card t₀.supp / 32))) hp0 hp1 (Real.exp_pos _).le hprob e
    have hu : 0 < Fintype.card t₀.supp := Fintype.card_pos_iff.mpr hFconnected.nonempty
    exact h.trans (anchored_red_palette_decay D _ (d : ℝ) p (by omega) hu hscale)
  have hbad : ∀ t : G.ConnectedComponent, (bitProductMeasure (Sym2 A) p hp0 hp1).real
      (paletteComponentBad (G.induce t.supp) d) ≤ 1 / 1000 := by
    intro t
    exact paletteComponentBad_probability_small (G.induce t.supp) d Δ L p ℓ hd hΔ hL
      (hcomponentCard t) (hcomponentMin t) (hcomponentMax t) hp0 hp1 hℓ hbase hentropy hlog hcomponent
  have hHbudget : (H.edgeSet.ncard : ℝ) ≤ Λ * G.edgeSet.ncard := by
    apply le_trans _ hK
    exact_mod_cast copy_edge_ncard_le (SimpleGraph.Copy.ofLE H K hHK)
  have hcost := palette_total_cost_budget D Λ (G.edgeSet.ncard : ℝ) (H.edgeSet.ncard : ℝ)
    hD (Nat.cast_nonneg _) hHbudget hΛD
  exact palette_avoiding_coloring_criterion G F K H hHK ⟨SimpleGraph.Copy.induce G t₀.supp⟩ hFedge
    heG d L k σ p (1 / (D : ℝ) ^ 2) hd (by omega) hσ hmin hcomponentCard hlocal hmargin
    c hcloc hcrep hp0 hp1 hred hbad hcost
    (palette_initial_pruning_capacity G K Δ D Λ hmax hK hcut)

end Erdos911
