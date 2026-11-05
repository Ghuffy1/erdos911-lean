import Erdos911.PaletteColoring
import Erdos911.DeletedEdgeCapacity
import Erdos911.HostDegreePruning

namespace Erdos911

/-- In a blue copy after the red-support recoloring, every edge missing
from the original blue palette was either outside the pruned host or was
explicitly recolored. -/
theorem palette_blue_copy_loss {V W A : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K H : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (c : W → A) (ω : Sym2 A → Bool) (S : Finset (Sym2 W))
    (f : G.Copy (K \ (paletteColorGraph H c ω false).deleteEdges (S : Set (Sym2 W)))) :
    letI : DecidableRel (paletteColorGraph H c ω true).Adj := Classical.decRel _
    (G \ copyRetainedGraph (paletteColorGraph H c ω true) f).edgeFinset.card ≤
      (copyRawEdges f ∩ (K \ H).edgeFinset).card + S.card := by
  classical
  let J := paletteColorGraph H c ω true
  have hkeep : ∀ u v, (K \ (paletteColorGraph H c ω false).deleteEdges (S : Set (Sym2 W))).Adj u v →
      s(u, v) ∉ (K \ H).edgeFinset ∪ S → J.Adj u v := by
    intro u v huv hnot
    have hnotLost : s(u, v) ∉ (K \ H).edgeFinset := fun h => hnot (Finset.mem_union_left _ h)
    have hnotS : s(u, v) ∉ S := fun h => hnot (Finset.mem_union_right _ h)
    have hH : H.Adj u v := by
      by_contra hn
      exact hnotLost ((K \ H).mem_edgeFinset.mpr ⟨huv.1, hn⟩)
    apply (paletteColorGraph_adj H c ω true u v).mpr
    refine ⟨hH, ?_⟩
    by_contra hn
    have hfalse : ω s(c u, c v) = false := Bool.eq_false_of_not_eq_true hn
    have hred := (paletteColorGraph_adj H c ω false u v).mpr ⟨hH, hfalse⟩
    exact huv.2 (SimpleGraph.deleteEdges_adj.mpr ⟨hred, hnotS⟩)
  have h := copy_missing_edges_le J f ((K \ H).edgeFinset ∪ S) hkeep
  exact h.trans (copy_capacity_union (copyRawEdges f) (K \ H).edgeFinset S)

end Erdos911
