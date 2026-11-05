import Erdos911.EdgeColorings
import Erdos911.RootedCounting

namespace Erdos911

def copyVertices {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) : Finset W :=
  Finset.univ.image f

theorem copyVertices_card {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) :
    (copyVertices f).card = Fintype.card V := by
  have hf : Function.Injective (f : V → W) := f.injective
  rw [copyVertices, Finset.card_image_of_injective _ hf, Finset.card_univ]

theorem copyVertices_ofLE_comp {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H J : SimpleGraph W} (hJ : J ≤ H) (f : G.Copy J) :
    copyVertices ((SimpleGraph.Copy.ofLE J H hJ).comp f) = copyVertices f := by
  rfl

theorem copyVertices_eq_subgraph_verts {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) :
    (copyVertices f : Set W) = f.toSubgraph.verts := by
  ext w
  simp [copyVertices, SimpleGraph.Copy.toSubgraph, SimpleGraph.Subgraph.map_verts]

theorem copyVertices_connected {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (hG : G.Connected) :
    (H.induce (copyVertices f : Set W)).Connected := by
  let h : G →g H.induce (copyVertices f : Set W) := {
    toFun := fun v => ⟨f v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
    map_rel' := fun hadj => map_rel f.toHom hadj }
  have hsurj : Function.Surjective h := by
    intro w
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp w.property
    exact ⟨v, Subtype.ext hv⟩
  exact SimpleGraph.Connected.map h hsurj hG

theorem copyVertices_mem_rooted {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (hG : G.Connected)
    (root : W) (hroot : root ∈ copyVertices f) :
    copyVertices f ∈ rootedConnectedSets H root (Fintype.card V) := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hroot, copyVertices_card f, copyVertices_connected f hG⟩

noncomputable def copyRawEdges {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) : Finset (Sym2 W) :=
  (copyHostEdges f).map ⟨Subtype.val, Subtype.val_injective⟩

theorem mem_copyRawEdges_iff_exists {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (e : Sym2 W) :
    e ∈ copyRawEdges f ↔ ∃ a : G.edgeSet, Sym2.map f a.val = e := by
  classical
  constructor
  · intro he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hb
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    apply Finset.mem_map.mpr
    exact ⟨f.mapEdgeSet a, Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩, rfl⟩

theorem copyRawEdges_ofLE_comp {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H J : SimpleGraph W} (hJ : J ≤ H) (f : G.Copy J) :
    copyRawEdges ((SimpleGraph.Copy.ofLE J H hJ).comp f) = copyRawEdges f := by
  ext e
  rw [mem_copyRawEdges_iff_exists, mem_copyRawEdges_iff_exists]
  rfl

theorem mem_copyHostEdges_iff {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (e : H.edgeSet) :
    e ∈ copyHostEdges f ↔ e.val ∈ f.toSubgraph.edgeSet := by
  classical
  rw [copyHostEdges_eq_subgraphHostEdges]
  simp only [subgraphHostEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_copyRawEdges_iff {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (e : Sym2 W) :
    e ∈ copyRawEdges f ↔ e ∈ f.toSubgraph.edgeSet := by
  classical
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    exact (mem_copyHostEdges_iff f a).mp ha
  · intro he
    let a : H.edgeSet := ⟨e, f.toSubgraph.edgeSet_subset he⟩
    exact Finset.mem_map.mpr ⟨a, (mem_copyHostEdges_iff f a).mpr he, rfl⟩

theorem copyRawEdges_card {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) :
    (copyRawEdges f).card = G.edgeSet.ncard := by
  classical
  rw [copyRawEdges, Finset.card_map, copyHostEdges_card]
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]

theorem copyRawEdges_image_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    ((Finset.univ : Finset (G.Copy H)).image copyRawEdges).card ≤ H.copyCount G := by
  classical
  let forget : Finset H.edgeSet → Finset (Sym2 W) :=
    fun S => S.map ⟨Subtype.val, Subtype.val_injective⟩
  calc
    ((Finset.univ : Finset (G.Copy H)).image copyRawEdges).card =
        (((Finset.univ : Finset (G.Copy H)).image copyHostEdges).image forget).card := by
      congr 1
      rw [Finset.image_image]
      rfl
    _ ≤ ((Finset.univ : Finset (G.Copy H)).image copyHostEdges).card := Finset.card_image_le
    _ ≤ H.copyCount G := copyHostEdges_image_card_le G H

theorem copy_subgraph_eq_of_images {V V' W : Type*} [Fintype V] [Fintype V']
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph V'} {H : SimpleGraph W}
    (f : G.Copy H) (g : G'.Copy H) (hverts : copyVertices f = copyVertices g)
    (hedges : copyRawEdges f = copyRawEdges g) : f.toSubgraph = g.toSubgraph := by
  apply SimpleGraph.Subgraph.ext
  · rw [← copyVertices_eq_subgraph_verts f, ← copyVertices_eq_subgraph_verts g, hverts]
  · funext u v
    apply propext
    change s(u, v) ∈ f.toSubgraph.edgeSet ↔ s(u, v) ∈ g.toSubgraph.edgeSet
    rw [← mem_copyRawEdges_iff, ← mem_copyRawEdges_iff, hedges]

/-- Vertex and edge images determine the isomorphism type of the copied graph. -/
theorem iso_of_copy_images {V V' W : Type*} [Fintype V] [Fintype V'] [Fintype W]
    [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph V'} {H : SimpleGraph W}
    (f : G.Copy H) (g : G'.Copy H) (hverts : copyVertices f = copyVertices g)
    (hedges : copyRawEdges f = copyRawEdges g) : Nonempty (G ≃g G') := by
  have heq := copy_subgraph_eq_of_images f g hverts hedges
  have eg : G' ≃g f.toSubgraph.coe := heq.symm ▸ g.isoToSubgraph
  exact ⟨f.isoToSubgraph.trans eg.symm⟩

end Erdos911
