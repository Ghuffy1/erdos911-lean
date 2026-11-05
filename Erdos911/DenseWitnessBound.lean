import Erdos911.DenseWitnessParameters
import Erdos911.HostObstruction

namespace Erdos911

theorem copy_edge_ncard_le {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  have h := Fintype.card_le_of_injective f.mapEdgeSet f.mapEdgeSet.injective
  simpa only [Set.fintypeCard_eq_ncard] using h

theorem edge_count_avoiding_coloring {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (hcount : H.edgeSet.ncard < G.edgeSet.ncard) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  have hfree : ¬G.IsContained H := by
    rintro ⟨f⟩
    exact (not_le_of_gt hcount) (copy_edge_ncard_le f)
  refine ⟨⊥, bot_le, ?_, ?_⟩
  · intro h
    exact hfree (h.trans ⟨SimpleGraph.Copy.ofLE _ H bot_le⟩)
  · simpa only [sdiff_bot] using hfree

/-- Any connected subgraph with average degree at least `d` forces a
size-Ramsey multiplier of `d / (4096 * log(Δ+1))` for the entire target. -/
theorem dense_witness_size_lower_bound {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (G : SimpleGraph U) [DecidableRel G.Adj]
    (hF : F.Connected) (hFG : F.IsContained G)
    (d Δ : ℕ) (hd : 4 ≤ d) (hdΔ : d ≤ Δ) (hdk : d ≤ Fintype.card V)
    (haverage : d * Fintype.card V ≤ 2 * F.edgeFinset.card)
    (hΔ : ∀ v, G.degree v ≤ Δ) :
    denseWitnessMultiplier d Δ * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  classical
  have hk : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hF.nonempty
  have hFedges : 0 < F.edgeFinset.card := by nlinarith
  have hFncard : 0 < F.edgeSet.ncard := by
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hFedges
  have hGedges : 0 < G.edgeSet.ncard := hFncard.trans_le (copy_edge_ncard_le hFG.some)
  have hGreal : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast hGedges
  apply (sizeRamsey_real_gt_iff G G (denseWitnessMultiplier d Δ * G.edgeSet.ncard)).mpr
  intro n H hbudget
  by_cases hlarge : 1 ≤ denseWitnessMultiplier d Δ
  · obtain ⟨hD, hp₀, hp₁, hscale, _, _⟩ := denseWitness_parameters d Δ hd hdΔ hlarge
    have hbudget' : (H.edgeFinset.card : ℝ) ≤ denseWitnessMultiplier d Δ * G.edgeSet.ncard := by
      simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] using hbudget
    have htotal := denseWitness_host_budget d Δ hd hdΔ hlarge
      (G.edgeSet.ncard : ℝ) H.edgeFinset.card hGreal hbudget'
    apply dense_witness_avoiding_coloring F G H hF hFG d Δ (denseWitnessCutoff d Δ)
      hd hdk hD haverage hΔ (denseWitnessMarkRate d Δ) hp₀ hp₁ hscale
    simpa only [Nat.cast_add, Nat.cast_one] using htotal
  · have hless : (H.edgeSet.ncard : ℝ) < G.edgeSet.ncard := by
      have h := mul_lt_mul_of_pos_right (lt_of_not_ge hlarge) hGreal
      linarith
    exact edge_count_avoiding_coloring G H (by exact_mod_cast hless)

end Erdos911
