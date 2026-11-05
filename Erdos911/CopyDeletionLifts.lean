import Erdos911.SeedMatchingObstruction

namespace Erdos911

/-- A copy using none of the deleted edges is also a copy in the
edge-deleted host, with exactly the same vertex map. -/
noncomputable def copyIntoDeleteEdges {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (K : Finset (Sym2 W))
    (havoid : Disjoint (copyRawEdges f) K) : F.Copy (H.deleteEdges (K : Set (Sym2 W))) where
  toHom := {
    toFun := f
    map_rel' := by
      intro u v huv
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨map_rel f.toHom huv, ?_⟩
      intro hK
      have hcopy : s(f u, f v) ∈ copyRawEdges f :=
        (mem_copyRawEdges_iff_exists f _).mpr ⟨⟨s(u, v), huv⟩, rfl⟩
      exact Finset.disjoint_left.mp havoid hcopy hK
  }
  injective' := f.injective

@[simp] theorem copyIntoDeleteEdges_apply {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (K : Finset (Sym2 W))
    (havoid : Disjoint (copyRawEdges f) K) (v : V) : copyIntoDeleteEdges f K havoid v = f v := rfl

@[simp] theorem copyRawEdges_copyIntoDeleteEdges {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (K : Finset (Sym2 W))
    (havoid : Disjoint (copyRawEdges f) K) : copyRawEdges (copyIntoDeleteEdges f K havoid) = copyRawEdges f := by
  ext e
  rw [mem_copyRawEdges_iff_exists, mem_copyRawEdges_iff_exists]
  rfl

@[simp] theorem copyVertices_copyIntoDeleteEdges {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (K : Finset (Sym2 W))
    (havoid : Disjoint (copyRawEdges f) K) : copyVertices (copyIntoDeleteEdges f K havoid) = copyVertices f := rfl

@[simp] theorem copyRetainedGraph_copyIntoDeleteEdges {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {H : SimpleGraph W} (J : SimpleGraph W) (f : F.Copy H) (K : Finset (Sym2 W))
    (havoid : Disjoint (copyRawEdges f) K) : copyRetainedGraph J (copyIntoDeleteEdges f K havoid) =
      copyRetainedGraph J f := rfl

end Erdos911
