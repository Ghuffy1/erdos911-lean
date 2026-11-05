import Erdos911.SupportTransfer
import Erdos911.BandParametersUniform
import Erdos911.BipartiteNeighborhoods

namespace Erdos911

/-- Exact right-degree normalization of the high part of a dyadic band.
The conclusion includes every degree bound and the retained edge fraction. -/
theorem exists_high_band_normalization {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V))
    (B q a : ℕ) (hq : 131072 ≤ q) (hlog : 1 ≤ Real.log (bandDegree q))
    (hgap : (bandDegree q : ℝ) * (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) ≤
      (bandDegree q : ℝ) / (2 * q) * bandLeftFloor q / 2)
    (ha : a ≤ bandDegree q ^ (B + 1))
    (hc : Real.exp 1 * Real.exp (-((bandDegree q : ℝ) / (2 * q : ℕ) * bandLeftFloor q) / 8) *
      ((a * (2 * q) : ℕ) + 1) ≤ 1)
    (hmin : ∀ v ∈ G.support, (q : ℝ) / 65536 ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ a)
    (hright : ∀ v ∈ right, G.degree v ≤ 2 * q)
    (hleft : ∀ v ∈ left, v ∈ G.support → bandLeftThreshold q / 8 < G.degree v)
    (he : 0 < G.edgeSet.ncard) :
    ∃ S : ↥(activeSide G right) → Finset ↥(activeSide G left),
      (incidenceGraph S).IsContained G ∧
      0 < Fintype.card (↥(activeSide G left) ⊕ ↥(activeSide G right)) ∧
      (∀ v, bandDegree q ≤ (incidenceGraph S).degree v) ∧
      (∀ v, (incidenceGraph S).degree v ≤ bandDegree q ^ (B + 1)) ∧
      (∀ y, (incidenceGraph S).degree (Sum.inr y) = bandDegree q) ∧
      (∀ x, (bandDegree q : ℝ) * (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) ≤
        (incidenceGraph S).degree (Sum.inl x)) ∧
      (G.edgeSet.ncard : ℝ) ≤ 262144 * (incidenceGraph S).edgeSet.ncard := by
  classical
  have hB' := activeSide_bipartite G left right hB
  have hfloor (v : V) (hv : v ∈ activeSide G left) : bandLeftFloor q ≤ G.degree v := by
    have h := hleft v ((mem_activeSide G left v).mp hv).1 ((mem_activeSide G left v).mp hv).2
    exact_mod_cast (Nat.floor_le_of_le (le_of_lt h) :
      Nat.floor (bandLeftThreshold q / 8) ≤ G.degree v)
  have hmin' (v : V) (hv : v ∈ G.support) : bandDegree q ≤ G.degree v := by
    have h := hmin v hv
    have hdiv : (bandDegree q : ℝ) ≤ (q : ℝ) / 65536 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 65536)]
      exact_mod_cast (Nat.div_mul_le_self q 65536)
    exact_mod_cast hdiv.trans h
  obtain ⟨S, hSG, hR, hL, _, hmass⟩ := exists_normalized_bipartite_copy G
    (activeSide G left) (activeSide G right) hB' (bandDegree q) a (2 * q) (bandLeftFloor q)
    (fun v hv => hmin' v ((mem_activeSide G right v).mp hv).2)
    (fun v _ => hmax v)
    (fun v hv => hright v ((mem_activeSide G right v).mp hv).1) hfloor hc
  have hleft' (x) : (bandDegree q : ℝ) * (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) ≤
      (incidenceGraph S).degree (Sum.inl x) := by
    apply hgap.trans
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hL x).le
  have hpow : 1 ≤ (Real.log (bandDegree q)) ^ (nearRegularDegreePower / 2) :=
    Real.one_le_rpow hlog (by norm_num [nearRegularDegreePower])
  have hmindegree : ∀ v, bandDegree q ≤ (incidenceGraph S).degree v := by
    intro v
    cases v with
    | inl x =>
      have h := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (α := ℝ) (bandDegree q))
      have h' : (bandDegree q : ℝ) ≤ (incidenceGraph S).degree (Sum.inl x) := by
        nlinarith only [h, hleft' x]
      exact_mod_cast h'
    | inr y => exact (hR y).ge
  have hmaxdegree : ∀ v, (incidenceGraph S).degree v ≤ bandDegree q ^ (B + 1) := by
    obtain ⟨f⟩ := hSG
    intro v
    exact (f.degree_le v).trans ((hmax (f v)).trans ha)
  have heR : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast he
  have hd : (0 : ℝ) < bandDegree q := by exact_mod_cast (bandDegree_bounds q hq).1
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hmass' : (G.edgeSet.ncard : ℝ) ≤ 262144 * (incidenceGraph S).edgeSet.ncard := by
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard] at hmass
    have hprob := (bandDegree_bounds q hq).2.2.2
    have hscaled : (bandDegree q : ℝ) / (2 * q) * G.edgeSet.ncard ≤
        (incidenceGraph S).edgeSet.ncard := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show (0 : ℝ) < 2 * q by positivity)).mpr
      simpa only [Nat.cast_mul, Nat.cast_ofNat, div_mul_eq_mul_div, mul_comm] using hmass
    have h := mul_le_mul_of_nonneg_right hprob heR.le
    nlinarith only [h, hscaled]
  have heS : 0 < (incidenceGraph S).edgeSet.ncard := by
    have h : (0 : ℝ) < (incidenceGraph S).edgeSet.ncard := by nlinarith only [heR, hmass']
    exact_mod_cast h
  have hcard : 0 < Fintype.card (↥(activeSide G left) ⊕ ↥(activeSide G right)) := by
    obtain ⟨e, he⟩ := (Set.ncard_pos (s := (incidenceGraph S).edgeSet)).mp heS
    induction e using Sym2.inductionOn with
    | _ u v => exact Fintype.card_pos_iff.mpr ⟨u⟩
  exact ⟨S, hSG, hcard, hmindegree, hmaxdegree, hR, hleft', hmass'⟩

end Erdos911
