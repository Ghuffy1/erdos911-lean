import Erdos911.UnbalancedNormalizationParameters
import Erdos911.MedianUpperPeeling
import Erdos911.BipartiteNeighborhoods
import Erdos911.SupportTransfer

namespace Erdos911

/-- A high-left-degree target with a cheap Ramsey bound has a normalized
incidence subtarget of constant edge mass. The left degree scale has no
upper bound; only its ratio to the maximum degree is controlled. -/
theorem unbalanced_median_normalization :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, ∀ m : ℕ, q ^ 3 ≤ m → ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], ∀ left right : Finset V,
      G.IsBipartiteWith (left : Set V) (right : Set V) →
      0 < G.edgeSet.ncard →
      (∀ v ∈ G.support, (q : ℝ) / 65536 ≤ G.degree v) →
      (∀ v ∈ left, v ∈ G.support → m ≤ G.degree v) →
      (∀ v ∈ right, G.degree v ≤ 2 * q) →
      ∀ Λ : ℝ, 1 ≤ Λ → Λ ≤ (q : ℝ) ^ 2 →
      (SimpleGraph.sizeRamsey G G : ℝ) ≤ Λ * G.edgeSet.ncard →
      ∃ (p : ℕ) (H : SimpleGraph V)
        (S : ↥(activeSide H right) → Finset ↥(activeSide H left)),
        m ≤ p ∧ H ≤ G ∧ (incidenceGraph S).IsContained G ∧
        0 < Fintype.card (↥(activeSide H left) ⊕ ↥(activeSide H right)) ∧
        (∀ y, (incidenceGraph S).degree (Sum.inr y) = unbalancedRightDegree q) ∧
        (∀ x, (p : ℝ) / 134217728 ≤ (incidenceGraph S).degree (Sum.inl x)) ∧
        (∀ v, ((incidenceGraph S).degree v : ℝ) ≤ 5 * Λ * p) ∧
        (G.edgeSet.ncard : ℝ) ≤ 67108864 * (incidenceGraph S).edgeSet.ncard := by
  obtain ⟨Q, hQ⟩ := unbalanced_normalization_eventually
  refine ⟨max Q 2097152, ?_⟩
  intro q hq m hm V _ _ G _ left right hB he hmin hleft hright Λ hΛ hΛq hRamsey
  classical
  have hqbase : 2097152 ≤ q := (le_max_right _ _).trans hq
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq2 : 2 * q ≤ q ^ 3 := by
    have hqr : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
    have hmul := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ (q : ℝ) ^ 2 by nlinarith only [hqr]) hqp.le
    exact_mod_cast (show (2 : ℝ) * q ≤ (q : ℝ) ^ 3 by nlinarith only [hmul])
  obtain ⟨p, _hp, hmp, _, hhalf, hmax⟩ := exists_bipartite_median_degree_bound G left right hB m Λ
    he (by linarith) hleft (fun v hv => (hright v hv).trans (hq2.trans hm)) hRamsey
  have hqp3 : q ^ 3 ≤ p := hm.trans hmp
  have hrp : (q : ℝ) / 65536 ≤ p := by
    have hqr : (q : ℝ) ≤ p := by exact_mod_cast ((show q ≤ 2 * q by omega).trans (hq2.trans hqp3))
    linarith only [hqr, hqp]
  obtain ⟨H, hHG, hHB, hHL, hHR, _, hHmass⟩ := exists_median_upper_peeling G left right hB p
    ((q : ℝ) / 65536) (by positivity) hrp hmin hhalf
  let : DecidableRel H.Adj := Classical.decRel _
  let A := activeSide H left
  let B := activeSide H right
  let a := unbalancedDegreeCap Λ p
  have hBip := activeSide_bipartite H left right hHB
  have hb : UnbalancedNormalizationBounds q p Λ := unbalanced_normalization_bounds q p Λ hqbase hqp3 hΛ hΛq
  have hHmax (v : V) : H.degree v ≤ a := by
    have hdeg : (H.degree v : ℝ) ≤ 4 * Λ * p :=
      (show (H.degree v : ℝ) ≤ G.degree v by exact_mod_cast (SimpleGraph.Copy.ofLE H G hHG).degree_le v).trans (hmax v)
    exact_mod_cast hdeg.trans hb.cutoff_lower
  have hHright (v : V) (hv : v ∈ B) : unbalancedRightDegree q ≤ H.degree v := by
    have hl := hHR v ((mem_activeSide H right v).mp hv).1 ((mem_activeSide H right v).mp hv).2
    have hfloor : (unbalancedRightDegree q : ℝ) ≤ (q : ℝ) / 1048576 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
      exact_mod_cast Nat.div_mul_le_self q 1048576
    have hreal : (unbalancedRightDegree q : ℝ) ≤ H.degree v := by
      rw [H.ncard_neighborSet] at hl
      linarith only [hfloor, hl]
    exact_mod_cast hreal
  have hHleft (v : V) (hv : v ∈ A) : unbalancedLeftFloor p ≤ H.degree v := by
    have hl := hHL v ((mem_activeSide H left v).mp hv).1 ((mem_activeSide H left v).mp hv).2
    have hfloor : (unbalancedLeftFloor p : ℝ) ≤ (p : ℝ) / 8 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
      exact_mod_cast Nat.div_mul_le_self p 8
    rw [H.ncard_neighborSet] at hl
    exact_mod_cast hfloor.trans hl
  have hHRmax (v : V) (hv : v ∈ B) : H.degree v ≤ 2 * q :=
    ((SimpleGraph.Copy.ofLE H G hHG).degree_le v).trans (hright v ((mem_activeSide H right v).mp hv).1)
  obtain ⟨S, hSH, hSright, hSleft, _, hSmass⟩ := exists_normalized_bipartite_copy H A B hBip
    (unbalancedRightDegree q) a (2 * q) (unbalancedLeftFloor p) hHright
    (fun v _ => hHmax v) hHRmax hHleft (hQ q ((le_max_left _ _).trans hq) p hqp3 Λ hΛ hΛq)
  obtain ⟨f⟩ := hSH
  have hSG : (incidenceGraph S).IsContained G := ⟨(SimpleGraph.Copy.ofLE H G hHG).comp f⟩
  have hSmax (v) : ((incidenceGraph S).degree v : ℝ) ≤ 5 * Λ * p := by
    have hdeg : (incidenceGraph S).degree v ≤ a := (f.degree_le v).trans (hHmax (f v))
    exact (show ((incidenceGraph S).degree v : ℝ) ≤ a by exact_mod_cast hdeg).trans hb.cutoff_upper
  have hSleft' (x) : (p : ℝ) / 134217728 ≤ (incidenceGraph S).degree (Sum.inl x) := by
    exact hb.left_lower.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hSleft x).le)
  have hSmass' : (G.edgeSet.ncard : ℝ) ≤ 67108864 * (incidenceGraph S).edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at hSmass
    have hfrac : (unbalancedRightDegree q : ℝ) / (2 * q) * H.edgeSet.ncard ≤
        (incidenceGraph S).edgeSet.ncard := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (2 : ℝ) * q)]
      simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hSmass
    have hfraclo := mul_le_mul_of_nonneg_right hb.right_fraction (Nat.cast_nonneg (α := ℝ) H.edgeSet.ncard)
    nlinarith only [hfrac, hfraclo, hHmass]
  have heR : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast he
  have heS : 0 < (incidenceGraph S).edgeSet.ncard := by
    have h : (0 : ℝ) < (incidenceGraph S).edgeSet.ncard := by nlinarith only [heR, hSmass']
    exact_mod_cast h
  have hcard : 0 < Fintype.card (↥A ⊕ ↥B) := by
    obtain ⟨e, he⟩ := (Set.ncard_pos (s := (incidenceGraph S).edgeSet)).mp heS
    induction e using Sym2.inductionOn with
    | _ u v => exact Fintype.card_pos_iff.mpr ⟨u⟩
  exact ⟨p, H, S, hmp, hHG, hSG, hcard, hSright, hSleft', hSmax, hSmass'⟩

end Erdos911
