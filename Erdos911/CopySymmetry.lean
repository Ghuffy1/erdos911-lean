import Erdos911.HostSupport
import Mathlib.Data.Fintype.Prod

namespace Erdos911

theorem copy_subgraph_precompose_iso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G.Copy H) (a : G ≃g G) :
    (f.comp a.toCopy).toSubgraph = f.toSubgraph := by
  change (⊤ : G.Subgraph).map (f.toHom.comp a.toHom) = (⊤ : G.Subgraph).map f.toHom
  rw [SimpleGraph.Subgraph.map_comp, SimpleGraph.Subgraph.map_iso_top]

theorem copy_precompose_iso_injective {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (f : G.Copy H) :
    Function.Injective (fun a : G ≃g G => f.comp a.toCopy) := by
  intro a b hab
  apply DFunLike.ext
  intro v
  exact f.injective (congrArg (fun c => c v) hab)

/-- Unlabelled subgraph copies multiplied by the target's automorphism count
are bounded by its labelled copies. -/
theorem copyCount_mul_aut_le {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    H.copyCount G * Nat.card (G ≃g G) ≤ Fintype.card (G.Copy H) := by
  classical
  let : Fintype (G ≃g G) :=
    Fintype.ofInjective (fun a : G ≃g G => (a : V → V)) DFunLike.coe_injective
  let S : Finset H.Subgraph :=
    (Finset.univ : Finset (G.Copy H)).image SimpleGraph.Copy.toSubgraph
  have hex : ∀ s : S, ∃ f : G.Copy H, f.toSubgraph = s.val := by
    intro s
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp s.property
    exact ⟨f, hf⟩
  choose f hf using hex
  let encode : S × (G ≃g G) → G.Copy H := fun p => (f p.1).comp p.2.toCopy
  have hinj : Function.Injective encode := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    have hst : s = t := by
      apply Subtype.ext
      calc
        s.val = ((f s).comp a.toCopy).toSubgraph := by
          rw [copy_subgraph_precompose_iso, hf]
        _ = ((f t).comp b.toCopy).toSubgraph := congrArg SimpleGraph.Copy.toSubgraph h
        _ = t.val := by rw [copy_subgraph_precompose_iso, hf]
    subst t
    have hab : a = b := copy_precompose_iso_injective (f s) h
    subst b
    rfl
  have hcard := Fintype.card_le_of_injective encode hinj
  rw [Fintype.card_prod, Fintype.card_coe] at hcard
  rw [SimpleGraph.copyCount_eq_card_image_copyToSubgraph, Nat.card_eq_fintype_card]
  exact hcard

theorem automorphism_count_pos {V : Type*} [Fintype V] (G : SimpleGraph V) :
    0 < Nat.card (G ≃g G) := by
  classical
  let : Fintype (G ≃g G) :=
    Fintype.ofInjective (fun a : G ≃g G => (a : V → V)) DFunLike.coe_injective
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨SimpleGraph.Iso.refl⟩

/-- A forest count for unlabelled copies, including their full symmetry
divisor. The target has no isolated vertices and contains an edge. -/
theorem graph_forest_unlabelled_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v) :
    (H.copyCount G : ℝ) ≤
      ((2 * H.edgeFinset.card : ℝ) ^ Nat.card G.ConnectedComponent *
        ((2 * H.edgeFinset.card : ℝ) /
          ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ)) ^
          (Fintype.card V - Nat.card G.ConnectedComponent) *
            (D : ℝ) ^ (Fintype.card V - Nat.card G.ConnectedComponent)) /
              Nat.card (G ≃g G) := by
  apply (le_div_iff₀ (by exact_mod_cast automorphism_count_pos G :
    (0 : ℝ) < Nat.card (G ≃g G))).mpr
  calc
    (H.copyCount G : ℝ) * Nat.card (G ≃g G) ≤ (Fintype.card (G.Copy H) : ℝ) := by
      exact_mod_cast copyCount_mul_aut_le G H
    _ ≤ _ := graph_forest_copy_bound_edges G H D hD hneighbors hedge

end Erdos911
