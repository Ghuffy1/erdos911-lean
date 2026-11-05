import Erdos911.OrderedForestConstruction
import Erdos911.OrderedForestBound
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fintype.Pi

namespace Erdos911

/-- The spanning-forest count for copies of an arbitrary finite target with
at least one edge. The number of roots is its actual component count. -/
theorem graph_forest_copy_bound {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (hedge : ∃ u v, G.Adj u v) :
    (Fintype.card (G.Copy H) : ℝ) ≤
      (Fintype.card W : ℝ) ^ Nat.card G.ConnectedComponent *
        ((2 * H.edgeFinset.card : ℝ) /
          ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ)) ^
          (Fintype.card V - Nat.card G.ConnectedComponent) *
            (D : ℝ) ^ (Fintype.card V - Nat.card G.ConnectedComponent) := by
  classical
  by_cases hzero : Fintype.card (G.Copy H) = 0
  · rw [hzero, Nat.cast_zero]
    positivity
  obtain ⟨f₀⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)
  obtain ⟨u, v, huv⟩ := hedge
  let : Nonempty W := ⟨f₀ u⟩
  have hhost : 0 < H.edgeFinset.card :=
    (map_rel f₀.toHom huv).degree_pos_left.trans_le (H.degree_le_card_edgeFinset (f₀ u))
  obtain ⟨e, parent, hparent, hroots, hchildren⟩ := exists_ordered_spanning_forest G
  have hsum := parentFiberCard_root_add_children parent
  have hless := components_lt_vertices_of_adj G ⟨u, v, huv⟩
  have hchildsum : (∑ j, parentFiberCard parent (some j)) =
      Fintype.card V - Nat.card G.ConnectedComponent := by omega
  have hchildpos : 0 < ∑ j, parentFiberCard parent (some j) := by omega
  let encode : G.Copy H → (Fin (Fintype.card V) → W) := fun f i => f (e i)
  let E : Finset (Fin (Fintype.card V) → W) := Finset.univ.image encode
  have hencode : Function.Injective encode := by
    intro f g h
    apply SimpleGraph.Copy.ext
    intro w
    obtain ⟨i, rfl⟩ := e.surjective w
    exact congrFun h i
  have hcard : E.card = Fintype.card (G.Copy H) := by
    change (Finset.univ.image encode).card = Fintype.card (G.Copy H)
    rw [Finset.card_image_of_injective _ hencode, Finset.card_univ]
  have hE_injective : ∀ x ∈ E, Function.Injective x := by
    intro x hx
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
    exact f.injective.comp e.injective
  have hE_edges : ∀ x ∈ E, ∀ i j, parent i = some j →
      H.Adj (initialSegment x i j) (x i) := by
    intro x hx i j hp
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
    change H.Adj (f (initialSegment (fun i => e i) i j)) (f (e i))
    exact map_rel f.toHom (hparent i j hp)
  have hbound := ordered_forest_embedding_count_of_child_bound H parent hhost hchildpos D
    (fun j => (hchildren j).trans (hD (e j))) E hE_injective hE_edges
  simpa only [hroots, hchildsum, hcard] using hbound

end Erdos911
