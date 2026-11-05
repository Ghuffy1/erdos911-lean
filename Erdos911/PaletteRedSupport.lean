import Erdos911.PaletteColoring
import Erdos911.AnchoredCopyCounting

open MeasureTheory

namespace Erdos911

noncomputable def paletteRedSupport {V W A : Type*}
    [Fintype V] [Fintype W] [DecidableEq A]
    (F : SimpleGraph V) (H : SimpleGraph W) (c : W → A) (ω : Sym2 A → Bool) : Finset H.edgeSet := by
  classical
  exact Finset.univ.biUnion (fun f : F.Copy H => if ω ∈ paletteRedEvent f c then copyHostEdges f else ∅)

theorem mem_paletteRedSupport {V W A : Type*}
    [Fintype V] [Fintype W] [DecidableEq A]
    (F : SimpleGraph V) (H : SimpleGraph W) (c : W → A) (ω : Sym2 A → Bool) (e : H.edgeSet) :
    e ∈ paletteRedSupport F H c ω ↔ ∃ f : F.Copy H, ω ∈ paletteRedEvent f c ∧ e ∈ copyHostEdges f := by
  classical
  simp only [paletteRedSupport, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf⟩
    by_cases hω : ω ∈ paletteRedEvent f c
    · exact ⟨f, hω, by simpa only [ite_eq_left hω] using hf⟩
    · simp only [ite_eq_right hω, Finset.notMem_empty] at hf
  · rintro ⟨f, hω, hf⟩
    exact ⟨f, by simpa only [ite_eq_left hω] using hf⟩

theorem paletteRedSupport_probability {V W A : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hF : F.Connected) (D : ℕ) (hD : ∀ w, H.degree w ≤ D) (c : W → A)
    (p B : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 ≤ B)
    (hprob : ∀ f : F.Copy H, (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteRedEvent f c) ≤ B)
    (e : H.edgeSet) :
    (bitProductMeasure (Sym2 A) p hp0 hp1).real {ω | e ∈ paletteRedSupport F H c ω} ≤
      (Fintype.card V * D ^ (2 * (Fintype.card V - 1)) : ℕ) * B := by
  classical
  let C := (Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyHostEdges f)
  have hsub : {ω | e ∈ paletteRedSupport F H c ω} ⊆ ⋃ f : ↥C, paletteRedEvent f.val c := by
    intro ω hω
    obtain ⟨f, hf, he⟩ := (mem_paletteRedSupport F H c ω e).mp hω
    exact Set.mem_iUnion.mpr ⟨⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩, hf⟩
  have hsum : (∑ f : ↥C, (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteRedEvent f.val c)) ≤
      C.card * B := by
    have h := Finset.sum_le_sum (fun f (_ : f ∈ (Finset.univ : Finset ↥C)) => hprob f.val)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] using h
  have hcount : C.card ≤ Fintype.card V * D ^ (2 * (Fintype.card V - 1)) :=
    copy_edge_incidence_bound F H hF D hD e
  exact (((measureReal_mono hsub).trans (measureReal_iUnion_fintype_le _)).trans hsum).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB)

noncomputable def paletteRedSupportRaw {V W A : Type*}
    [Fintype V] [Fintype W] [DecidableEq A]
    (F : SimpleGraph V) (H : SimpleGraph W) (c : W → A) (ω : Sym2 A → Bool) : Finset (Sym2 W) :=
  (paletteRedSupport F H c ω).map ⟨Subtype.val, Subtype.val_injective⟩

theorem paletteRedSupportRaw_card {V W A : Type*}
    [Fintype V] [Fintype W] [DecidableEq A]
    (F : SimpleGraph V) (H : SimpleGraph W) (c : W → A) (ω : Sym2 A → Bool) :
    (paletteRedSupportRaw F H c ω).card = (paletteRedSupport F H c ω).card := Finset.card_map _

theorem paletteRedSupportRaw_avoids {V W A : Type*}
    [Fintype V] [Fintype W] [DecidableEq A]
    (F : SimpleGraph V) (H : SimpleGraph W) (c : W → A) (ω : Sym2 A → Bool)
    (hedge : ∃ u v, F.Adj u v) :
    ¬F.IsContained ((paletteColorGraph H c ω false).deleteEdges
      (paletteRedSupportRaw F H c ω : Set (Sym2 W))) := by
  classical
  rintro ⟨f⟩
  let fR : F.Copy (paletteColorGraph H c ω false) :=
    (SimpleGraph.Copy.ofLE _ _ (SimpleGraph.deleteEdges_le _)).comp f
  let fH : F.Copy H := (SimpleGraph.Copy.ofLE _ _ (paletteColorGraph_le H c ω false)).comp fR
  have hred : ω ∈ paletteRedEvent fH c := paletteRedEvent_of_colored_copy F H c ω fR
  obtain ⟨u, v, huv⟩ := hedge
  let a : F.edgeSet := ⟨s(u, v), huv⟩
  let e : H.edgeSet := fH.mapEdgeSet a
  have hecopy : e ∈ copyHostEdges fH := Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have he : e ∈ paletteRedSupport F H c ω := (mem_paletteRedSupport F H c ω e).mpr ⟨fH, hred, hecopy⟩
  have heraw : e.val ∈ paletteRedSupportRaw F H c ω := Finset.mem_map.mpr ⟨e, he, rfl⟩
  have hnot := (SimpleGraph.deleteEdges_adj.mp (map_rel f.toHom huv)).2
  exact hnot heraw

end Erdos911
