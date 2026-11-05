import Erdos911.ExplicitPaletteParameters

namespace Erdos911

/-- The sparse bounded-component theorem with the coloring parameters
fully discharged by explicit hypotheses on degree and component order. -/
theorem quantitative_sparse_palette_ramsey {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d Δ L : ℕ) (Λ σ : ℝ)
    (hV : 0 < Fintype.card V) (hd : 1 ≤ d) (hdΔ : d ≤ Δ) (hL : 1 ≤ L)
    (hΛ : 1 ≤ Λ) (hσ : 0 ≤ σ) (hσd : σ ≤ 128 * d)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (horder : ∀ t : G.ConnectedComponent, Nat.card t.supp ≤ L)
    (hlocal : ∀ S : Finset V, S.card ≤ L →
      ((G.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hscale : Real.exp 1 * sparsePaletteConstant * paletteDensityLog Λ Δ ≤ d)
    (hlogorder : Real.log L ≤ (d : ℝ) / 1280 *
      Real.log ((d : ℝ) / (sparsePaletteConstant * paletteDensityLog Λ Δ))) :
    Λ * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨P⟩ := explicit_sparse_palette_parameters d Δ L Λ σ hd hdΔ hL hΛ hσ hσd hscale hlogorder
  exact sparse_palette_size_ramsey_bound G d Δ L P.D P.k Λ σ P.p P.gap
    hV (by omega) (hd.trans hdΔ) (by omega) P.large_cutoff P.large_reciprocal hΛ
    P.multiplier_le hσ P.probability_nonneg P.probability_le_one P.gap_nonneg hmin hmax
    horder hlocal P.collision_margin P.cutoff_bound P.red_scale P.blue_base P.entropy_bound
    P.geometric_bound P.component_bound

end Erdos911
