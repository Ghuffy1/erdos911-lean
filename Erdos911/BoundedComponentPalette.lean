import Erdos911.DensePaletteParameters
import Erdos911.DenseCoreDichotomy
import Erdos911.CopyComponentOrder

namespace Erdos911

universe u

/-- A uniform quantitative Ramsey lower bound for graphs whose connected
components have bounded order. No local density hypothesis remains. -/
theorem bounded_component_palette_ramsey (d Δ L : ℕ) (Λ : ℝ)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 0 < Fintype.card V) (hd : 1 ≤ d) (hdΔ : d ≤ Δ) (hL : 1 ≤ L) (hΛ : 1 ≤ Λ)
    (hmin : ∀ v, d ≤ G.degree v) (hmax : ∀ v, G.degree v ≤ Δ)
    (horder : ∀ t : G.ConnectedComponent, Nat.card t.supp ≤ L)
    (hscale : Real.exp 1 * boundedPaletteConstant * paletteDensityLog Λ Δ ≤ d)
    (hlogorder : Real.log L ≤ (d : ℝ) / 8192 *
      Real.log ((d : ℝ) / (boundedPaletteConstant * paletteDensityLog Λ Δ))) :
    Λ * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  classical
  have main : ∀ n : ℕ, ∀ d : ℕ, Δ - d = n →
      ∀ (W : Type u) [Fintype W] [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj],
      ∀ Λ : ℝ, 0 < Fintype.card W → 1 ≤ d → d ≤ Δ → 1 ≤ Λ →
      (∀ v, d ≤ F.degree v) → (∀ v, F.degree v ≤ Δ) →
      (∀ t : F.ConnectedComponent, Nat.card t.supp ≤ L) →
      Real.exp 1 * boundedPaletteConstant * paletteDensityLog Λ Δ ≤ d →
      Real.log L ≤ (d : ℝ) / 8192 *
        Real.log ((d : ℝ) / (boundedPaletteConstant * paletteDensityLog Λ Δ)) →
      Λ * F.edgeSet.ncard < (SimpleGraph.sizeRamsey F F : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hn W _ _ F _ Λ hW hd hdΔ hΛ hmin hmax horder hscale hlogorder
      have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hΛ0 : 0 ≤ Λ := by linarith
      have heF : 0 < F.edgeSet.ncard := by
        obtain ⟨v⟩ := Fintype.card_pos_iff.mp hW
        have hp : 0 < F.degree v := (show 0 < d by omega).trans_le (hmin v)
        have he := hp.trans_le (F.degree_le_card_edgeFinset v)
        simpa only [F.edgeFinset_card, Set.fintypeCard_eq_ncard] using he
      have heFR : (0 : ℝ) < F.edgeSet.ncard := by exact_mod_cast heF
      rcases dense_core_or_locally_sparse_target F d Δ L (16 * d) hmin hmax with
        ⟨U, J, hJF, hJmin, hJorder, hmass⟩ | ⟨U, J, hJF, hJmin, hJmax, hJlocal, hmass⟩
      · let : Fintype U := Fintype.ofFinite _
        let : DecidableRel J.Adj := Classical.decRel _
        obtain ⟨f⟩ := hJF
        have heJ : 0 < J.edgeSet.ncard := by
          by_contra h
          have hz : J.edgeSet.ncard = 0 := by omega
          rw [hz, Nat.cast_zero, mul_zero] at hmass
          push_cast at hmass
          nlinarith only [hmass, heFR, hdp]
        have hU : 0 < Fintype.card U := by
          by_contra h
          have hz : Fintype.card U = 0 := by omega
          let : IsEmpty U := Fintype.card_eq_zero_iff.mp hz
          have hzJ : J = ⊥ := Subsingleton.elim _ _
          simp only [hzJ, SimpleGraph.edgeSet_bot, Set.ncard_empty] at heJ
          omega
        have hJmax : ∀ v, J.degree v ≤ Δ := fun v => (f.degree_le v).trans (hmax (f v))
        have hJmin' : ∀ v, 16 * d ≤ J.degree v := by
          simpa only [SimpleGraph.ncard_neighborSet] using hJmin
        have hsΔ : 16 * d ≤ Δ := by
          obtain ⟨v⟩ := Fintype.card_pos_iff.mp hU
          exact (hJmin' v).trans (hJmax v)
        let Λ' := (Δ : ℝ) * Λ / (2 * d)
        obtain ⟨hΛ', hscale', hlogorder'⟩ :=
          bounded_palette_dense_parameters d Δ L Λ hd hsΔ hΛ hscale hlogorder
        have hn' : Δ - 16 * d < n := by omega
        have hJ := ih (Δ - 16 * d) hn' (16 * d) rfl U J Λ' hU (by omega) hsΔ hΛ'
          hJmin' hJmax hJorder hscale' hlogorder'
        have hbudget : Λ * F.edgeSet.ncard ≤ Λ' * J.edgeSet.ncard := by
          dsimp only [Λ']
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < 2 * (d : ℝ))]
          have hm := mul_le_mul_of_nonneg_left hmass hΛ0
          push_cast at hm
          nlinarith only [hm]
        have hmono : (SimpleGraph.sizeRamsey J J : ℝ) ≤ SimpleGraph.sizeRamsey F F := by
          exact_mod_cast sizeRamsey_mono ⟨f⟩ ⟨f⟩
        exact hbudget.trans_lt (hJ.trans_le hmono)
      · let : Fintype U := Fintype.ofFinite _
        let : DecidableRel J.Adj := Classical.decRel _
        obtain ⟨f⟩ := hJF
        have heJ : 0 < J.edgeSet.ncard := by
          have heJR : (0 : ℝ) < J.edgeSet.ncard := lt_of_lt_of_le (by positivity) hmass
          exact_mod_cast heJR
        have hU : 0 < Fintype.card U := by
          by_contra h
          have hz : Fintype.card U = 0 := by omega
          let : IsEmpty U := Fintype.card_eq_zero_iff.mp hz
          have hzJ : J = ⊥ := Subsingleton.elim _ _
          simp only [hzJ, SimpleGraph.edgeSet_bot, Set.ncard_empty] at heJ
          omega
        obtain ⟨hq, hσq, hscaleq, hlogq⟩ :=
          bounded_palette_sparse_parameters d Δ L Λ hd hdΔ hΛ hscale hlogorder
        have hJ := quantitative_sparse_palette_ramsey J (d / 4) Δ L (4 * Λ) (16 * d)
          hU hq (by omega) hL (by linarith) (by positivity) hσq
          (by simpa only [SimpleGraph.ncard_neighborSet] using hJmin)
          (by simpa only [SimpleGraph.ncard_neighborSet] using hJmax)
          (component_order_of_copy f L horder) (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hJlocal)
          hscaleq hlogq
        have hbudget : Λ * F.edgeSet.ncard ≤ (4 * Λ) * J.edgeSet.ncard := by
          have hm := mul_le_mul_of_nonneg_left hmass hΛ0
          nlinarith only [hm]
        have hmono : (SimpleGraph.sizeRamsey J J : ℝ) ≤ SimpleGraph.sizeRamsey F F := by
          exact_mod_cast sizeRamsey_mono ⟨f⟩ ⟨f⟩
        exact hbudget.trans_lt (hJ.trans_le hmono)
  exact main (Δ - d) d rfl V G Λ hV hd hdΔ hΛ hmin hmax horder hscale hlogorder

end Erdos911
