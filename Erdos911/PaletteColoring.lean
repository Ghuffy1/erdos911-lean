import Erdos911.PaletteCopies
import Erdos911.PaletteMapTails

namespace Erdos911

def paletteColorGraph {W A : Type*} (H : SimpleGraph W) (c : W → A)
    (ω : Sym2 A → Bool) (b : Bool) : SimpleGraph W :=
  edgeColorClass H (fun e => ω (Sym2.map c e.val)) b

theorem paletteColorGraph_adj {W A : Type*} (H : SimpleGraph W) (c : W → A)
    (ω : Sym2 A → Bool) (b : Bool) (u v : W) :
    (paletteColorGraph H c ω b).Adj u v ↔ H.Adj u v ∧ ω s(c u, c v) = b := by
  constructor
  · rintro ⟨h, hb⟩
    exact ⟨h, hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨h, hb⟩

theorem paletteColorGraph_le {W A : Type*} (H : SimpleGraph W) (c : W → A)
    (ω : Sym2 A → Bool) (b : Bool) : paletteColorGraph H c ω b ≤ H :=
  edgeColorClass_le _ _ _

theorem paletteColorGraph_complement {W A : Type*} (H : SimpleGraph W) (c : W → A)
    (ω : Sym2 A → Bool) : H \ paletteColorGraph H c ω false = paletteColorGraph H c ω true :=
  edgeColorClass_complement _ _

def retainedGraphCopy {V W : Type*} {F : SimpleGraph V} {K : SimpleGraph W}
    (H : SimpleGraph W) (f : F.Copy K) : (copyRetainedGraph H f).Copy H where
  toHom := { toFun := f, map_rel' := fun h => h.2 }
  injective' := f.injective

noncomputable def paletteRedEvent {V W A : Type*} [Fintype V] [Fintype W] [DecidableEq A]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (c : W → A) : Set (Sym2 A → Bool) :=
  fixedBits ((copyRawEdges f).image (Sym2.map c)) false

theorem paletteRedEvent_of_colored_copy {V W A : Type*}
    [Fintype V] [Fintype W] [DecidableEq A]
    (F : SimpleGraph V) (H : SimpleGraph W) (c : W → A) (ω : Sym2 A → Bool)
    (f : F.Copy (paletteColorGraph H c ω false)) :
    ω ∈ paletteRedEvent ((SimpleGraph.Copy.ofLE _ _ (paletteColorGraph_le H c ω false)).comp f) c := by
  classical
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨b, rfl⟩ := (mem_copyRawEdges_iff_exists _ a).mp ha
  obtain ⟨b, hb⟩ := b
  induction b using Sym2.inductionOn with
  | _ u v =>
    exact ((paletteColorGraph_adj H c ω false (f u) (f v)).mp (map_rel f.toHom hb)).2

theorem paletteRedEvent_probability {V W A : Type*}
    [Fintype V] [Fintype W] [Fintype A] [DecidableEq A]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (c : W → A)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteRedEvent f c) =
      (1 - p) ^ ((copyRawEdges f).image (Sym2.map c)).card := by
  rw [paletteRedEvent, bitProductMeasure_fixedBits]
  simp only [bernoulliWeight, Bool.false_eq_true, ite_false]

end Erdos911
