import Erdos911.CopyDensity

namespace Erdos911

/-- A graph copy sends each connected component injectively into one
connected component of its host. In particular component order bounds
survive all subtarget reductions, including those that split components. -/
theorem component_order_of_copy {V W : Type*} [Finite V] [Finite W]
    {F : SimpleGraph V} {G : SimpleGraph W} (f : F.Copy G) (L : ℕ)
    (horder : ∀ c : G.ConnectedComponent, Nat.card c.supp ≤ L)
    (c : F.ConnectedComponent) : Nat.card c.supp ≤ L := by
  classical
  obtain ⟨v, hv⟩ := c.nonempty_supp
  let t := G.connectedComponentMk (f v)
  have hmem (w : c.supp) : f w.val ∈ t.supp := by
    have hr := (c.reachable_of_mem_supp hv w.property).map f.toHom
    change G.connectedComponentMk (f w.val) = G.connectedComponentMk (f v)
    exact (SimpleGraph.ConnectedComponent.eq.mpr hr).symm
  let g : c.supp → t.supp := fun w => ⟨f w.val, hmem w⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective g hg).trans (horder t)

end Erdos911
