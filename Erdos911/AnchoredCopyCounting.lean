import Erdos911.CopyImages

namespace Erdos911

noncomputable def copiesAtVertex {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) : Finset (F.Copy H) := by
  classical
  exact Finset.univ.filter (fun f => root ∈ copyVertices f)

theorem mem_copiesAtVertex {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) (f : F.Copy H) :
    f ∈ copiesAtVertex F H root ↔ root ∈ copyVertices f := by
  classical
  simp only [copiesAtVertex, Finset.mem_filter, Finset.mem_univ, true_and]

theorem copiesAtVertex_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (D : ℕ) (hD : ∀ w, H.degree w ≤ D) (root : W) :
    (copiesAtVertex F H root).card ≤ Fintype.card V * D ^ (2 * (Fintype.card V - 1)) := by
  classical
  let fibers (v : V) : Finset (F.Copy H) := Finset.univ.filter (fun f => f v = root)
  have hsub : copiesAtVertex F H root ⊆ Finset.univ.biUnion fibers := by
    intro f hf
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ((mem_copiesAtVertex F H root f).mp hf)
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  have hfibers : ∀ v, (fibers v).card ≤ D ^ (2 * (Fintype.card V - 1)) := by
    intro v
    have h := rooted_copy_count F H hF D hD v root
    simpa only [Fintype.card_subtype] using h
  calc
    (copiesAtVertex F H root).card ≤ (Finset.univ.biUnion fibers).card := Finset.card_le_card hsub
    _ ≤ ∑ v, (fibers v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : V, D ^ (2 * (Fintype.card V - 1)) := Finset.sum_le_sum (fun v _ => hfibers v)
    _ = Fintype.card V * D ^ (2 * (Fintype.card V - 1)) := by simp

/-- The number of copies using one host edge is controlled by rooting a
source vertex at one fixed endpoint of that edge. -/
theorem copy_edge_incidence_bound {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (D : ℕ) (hD : ∀ w, H.degree w ≤ D) (e : H.edgeSet) :
    ((Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyHostEdges f)).card ≤
      Fintype.card V * D ^ (2 * (Fintype.card V - 1)) := by
  classical
  have hsub : ((Finset.univ : Finset (F.Copy H)).filter (fun f => e ∈ copyHostEdges f)) ⊆
      copiesAtVertex F H e.val.out.1 := by
    intro f hf
    have hes := (mem_copyHostEdges_iff f e).mp (Finset.mem_filter.mp hf).2
    have hv := SimpleGraph.Subgraph.mem_verts_of_mem_edge hes (Sym2.out_fst_mem e.val)
    rw [← copyVertices_eq_subgraph_verts f] at hv
    exact (mem_copiesAtVertex F H e.val.out.1 f).mpr hv
  exact (Finset.card_le_card hsub).trans (copiesAtVertex_card_le F H hF D hD _)

end Erdos911
