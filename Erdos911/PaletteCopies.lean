import Erdos911.CollisionSafePalette
import Erdos911.CopyDensity

namespace Erdos911

theorem repeatedVertices_image {V W A : Type*} [DecidableEq W]
    (S : Finset V) (f : V → W) (hf : Function.Injective f) (c : W → A) :
    repeatedVertices (S.image f) c = (repeatedVertices S (c ∘ f)).image f := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨hwS, y, hyS, hyw, hcolors⟩ := (mem_repeatedVertices (S.image f) c w).mp hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hwS
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hyS
    refine Finset.mem_image.mpr ⟨v, (mem_repeatedVertices S (c ∘ f) v).mpr ?_, rfl⟩
    exact ⟨hv, u, hu, fun h => hyw (congrArg f h), hcolors⟩
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hvS, u, huS, huv, hcolors⟩ := (mem_repeatedVertices S (c ∘ f) v).mp hv
    refine (mem_repeatedVertices (S.image f) c (f v)).mpr
      ⟨Finset.mem_image.mpr ⟨v, hvS, rfl⟩, f u, Finset.mem_image.mpr ⟨u, huS, rfl⟩, ?_, hcolors⟩
    exact fun h => huv (hf h)

theorem repeatedVertices_image_card {V W A : Type*} [DecidableEq W]
    (S : Finset V) (f : V → W) (hf : Function.Injective f) (c : W → A) :
    (repeatedVertices (S.image f) c).card = (repeatedVertices S (c ∘ f)).card := by
  rw [repeatedVertices_image S f hf c, Finset.card_image_of_injective _ hf]

theorem induced_image_connected {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {G : SimpleGraph W} (f : F.Copy G) (S : Finset V)
    (hconn : (F.induce (S : Set V)).Connected) :
    (G.induce (S.image f : Set W)).Connected := by
  let c := copyInduceImage f S
  apply SimpleGraph.Connected.map c.toHom _ hconn
  intro w
  obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp w.property
  exact ⟨⟨v, hv⟩, Subtype.ext heq⟩

/-- The palette's collision bound transfers to each connected vertex
set in an embedded target, with exactly the same cardinality bound. -/
theorem palette_collision_bound_for_copy {V W A : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {G : SimpleGraph W} (f : F.Copy G) (c : W → A)
    (K k : ℕ)
    (hc : ∀ S : Finset W, S.card ≤ K → (G.induce (S : Set W)).Connected →
      k * (repeatedVertices S c).card ≤ 2 * S.card)
    (S : Finset V) (hsize : S.card ≤ K) (hconn : (F.induce (S : Set V)).Connected) :
    k * (repeatedVertices S (c ∘ f)).card ≤ 2 * S.card := by
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S f.injective
  have h := hc (S.image f) (hcard ▸ hsize) (induced_image_connected f S hconn)
  rwa [repeatedVertices_image_card S f f.injective c, hcard] at h

theorem locally_injective_palette_for_copy {V W A : Type*}
    {F : SimpleGraph V} {G : SimpleGraph W} (f : F.Copy G) (c : W → A)
    (hc : ∀ u v w, G.Adj u v → G.Adj u w → c v = c w → v = w) :
    ∀ u v w, F.Adj u v → F.Adj u w → (c ∘ f) v = (c ∘ f) w → v = w := by
  intro u v w huv huw hcolors
  exact f.injective (hc (f u) (f v) (f w) (map_rel f.toHom huv) (map_rel f.toHom huw) hcolors)

end Erdos911
