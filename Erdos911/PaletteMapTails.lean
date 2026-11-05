import Erdos911.BinomialMarkTail
import Erdos911.PaletteEdgeCapacity

open MeasureTheory

namespace Erdos911

def degreeVolume {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset V) : ℕ := ∑ v ∈ S, F.degree v

theorem degreeVolume_real {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset V) : (degreeVolume F S : ℝ) = ∑ v ∈ S, (F.degree v : ℝ) := by
  simp only [degreeVolume, Nat.cast_sum]

theorem degreeVolume_minimum {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (d : ℕ) (hmin : ∀ v, d ≤ F.degree v) (S : Finset V) : d * S.card ≤ degreeVolume F S := by
  calc
    d * S.card = ∑ _v ∈ S, d := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun v _ => hmin v)

theorem induced_edges_le_half_volume {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) :
    2 * (F.induce (S : Set V)).edgeSet.ncard ≤ degreeVolume F S := by
  classical
  let J := F.induce (S : Set V)
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset ↥(S : Set V))) =>
    (SimpleGraph.Copy.induce F (S : Set V)).degree_le v)
  change (∑ v : ↥(S : Set V), J.degree v) ≤ ∑ v : ↥(S : Set V), F.degree v.val at hsum
  rw [J.sum_degrees_eq_twice_card_edges, J.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
  have hright : (∑ v : ↥(S : Set V), F.degree v.val) = ∑ v ∈ S, F.degree v :=
    (Finset.sum_subtype S (fun _ => Iff.rfl) (fun v => F.degree v)).symm
  rw [hright] at hsum
  exact hsum

noncomputable def inducedLabelPairs {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) (f : ↥S → A) : Finset (Sym2 A) :=
  (F.induce (S : Set V)).edgeFinset.image (Sym2.map f)

theorem inducedLabelPairs_card_bound {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) (f : ↥S → A) :
    2 * (inducedLabelPairs F S f).card ≤ degreeVolume F S := by
  have hcard : (inducedLabelPairs F S f).card ≤ (F.induce (S : Set V)).edgeSet.ncard := by
    apply Finset.card_image_le.trans_eq
    rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  exact (Nat.mul_le_mul_left 2 hcard).trans (induced_edges_le_half_volume F S)

noncomputable def paletteMapThreshold {V : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) : ℕ :=
  Nat.ceil ((degreeVolume F S : ℝ) / 32)

theorem paletteMapThreshold_bounds {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V)
    (hvolume : 0 < degreeVolume F S) (f : ↥S → A) :
    0 < paletteMapThreshold F S ∧ (inducedLabelPairs F S f).card ≤ 16 * paletteMapThreshold F S := by
  have hpos : (0 : ℝ) < (degreeVolume F S : ℝ) / 32 := by
    have h : (0 : ℝ) < degreeVolume F S := by exact_mod_cast hvolume
    positivity
  have hceil : (degreeVolume F S : ℝ) / 32 ≤ paletteMapThreshold F S := Nat.le_ceil _
  have hbound : (2 : ℝ) * (inducedLabelPairs F S f).card ≤ degreeVolume F S := by
    exact_mod_cast inducedLabelPairs_card_bound F S f
  constructor
  · have h : (0 : ℝ) < paletteMapThreshold F S := hpos.trans_le hceil
    exact_mod_cast h
  · have h : ((inducedLabelPairs F S f).card : ℝ) ≤ 16 * paletteMapThreshold F S := by
      nlinarith only [hceil, hbound]
    exact_mod_cast h

noncomputable def bluePaletteMapEvent {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V) (f : ↥S → A) : Set (Sym2 A → Bool) :=
  {ω | paletteMapThreshold F S ≤ (markedElements (inducedLabelPairs F S f) ω).card}

theorem bluePaletteMapEvent_probability {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V)
    (hvolume : 0 < degreeVolume F S) (f : ↥S → A)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitProductMeasure (Sym2 A) p hp0 hp1).real (bluePaletteMapEvent F S f) ≤
      (16 * Real.exp 1 * p) ^ paletteMapThreshold F S := by
  obtain ⟨ht, hcard⟩ := paletteMapThreshold_bounds F S hvolume f
  exact marked_elements_tail_ratio (inducedLabelPairs F S f) (paletteMapThreshold F S) 16 ht hcard p hp0 hp1

/-- Union over all label maps on a fixed vertex set. Only the set order,
not the ambient target order, occurs in the number of maps. -/
theorem exists_bluePaletteMap_probability {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (S : Finset V)
    (hvolume : 0 < degreeVolume F S) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitProductMeasure (Sym2 A) p hp0 hp1).real (⋃ f : ↥S → A, bluePaletteMapEvent F S f) ≤
      (Fintype.card A : ℝ) ^ S.card * (16 * Real.exp 1 * p) ^ paletteMapThreshold F S := by
  have h := (measureReal_iUnion_fintype_le (μ := bitProductMeasure (Sym2 A) p hp0 hp1)
    (fun f : ↥S → A => bluePaletteMapEvent F S f)).trans
      (Finset.sum_le_sum (fun f _ => bluePaletteMapEvent_probability F S hvolume f p hp0 hp1))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
    nsmul_eq_mul, Nat.cast_pow] using h

end Erdos911
