import Erdos911.BaselineResidualParameters
import Erdos911.SampledOrdinaryAssignments

namespace Erdos911

/-- Uniform polynomial-degree version of the residual-edge obstruction.
The remaining assumptions describe the actual graph geometry and the
number of edges retained in each target copy. -/
theorem polynomial_sparse_residual_obstruction {W : Type*} [Fintype W] [DecidableEq W]
    (A : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
      (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj],
      F.Connected → J ≤ H → ∀ D b : ℕ,
      (∀ v, d ≤ F.degree v) → (∀ v, F.degree v ≤ D) →
      (∀ w, H.degree w ≤ D) → D ≤ d ^ A →
      (d : ℝ) * n / 8 ≤ b →
      (∀ S T : Finset W, S.card = baselineBlockSize d → T.card = baselineBlockSize d →
        Disjoint S T → (crossEdges J S T : ℝ) ≤
          (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d) →
      (∀ f : F.Copy H, b + 17 * (F \ copyRetainedGraph J f).edgeFinset.card ≤ F.edgeFinset.card) →
      ∃ marked : Finset (Sym2 W), marked ⊆ J.edgeFinset ∧
        (marked.card : ℝ) ≤ 512 * Real.log (Real.log d) / d * J.edgeFinset.card ∧
        ¬F.IsContained (H.deleteEdges (marked : Set (Sym2 W))) := by
  obtain ⟨d₀, hd₀⟩ := baseline_residual_parameters_uniform A
  refine ⟨d₀, ?_⟩
  intro d hd n F _ H J _ _ hF hJ D b hmin hmax hhost hDpow hb hnodense hlarge
  obtain ⟨v⟩ := hF.nonempty
  have hdn : d ≤ n := by
    simpa only [Fintype.card_fin] using (hmin v).trans (F.degree_lt_card_verts v).le
  have hdD : d ≤ D := (hmin v).trans (hmax v)
  obtain ⟨hd4, hq, hsmall, hgap, hα₀, hα₁, hp₀, hp₁, _, hseed, hlog⟩ :=
    hd₀ d hd D hdD hDpow n hdn b hb
  obtain ⟨marked, hmarked, hcost, hfree⟩ := finite_sparse_residual_obstruction F H J hF hJ
    d D (baselineSeedOrder A d n) (baselineBlockSize d) b (by omega) hmin hmax hhost
    (by omega) hq hsmall (1 / 4) (baselineSampleRate A d) (baselineResidualRate d)
    (by norm_num) hα₀ hα₁ hp₀ hp₁ hgap hnodense hseed hlarge hlog
  refine ⟨marked, hmarked, ?_, hfree⟩
  calc
    (marked.card : ℝ) ≤ 2 * baselineResidualRate d * J.edgeFinset.card := hcost
    _ = _ := by unfold baselineResidualRate; ring

end Erdos911
