import Erdos911.TargetPatternGraph
import Erdos911.ConnectedLabelWeights

namespace Erdos911

noncomputable def componentImage {A V : Type*} [Fintype A] [DecidableEq V]
    (P : SimpleGraph A) (g : A → V) (c : P.ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset.image g

theorem mem_componentImage {A V : Type*} [Fintype A] [DecidableEq V]
    (P : SimpleGraph A) (g : A → V) (c : P.ConnectedComponent) (v : V) :
    v ∈ componentImage P g c ↔ ∃ x ∈ c.supp, g x = v := by
  classical
  simp only [componentImage, Finset.mem_image, Set.mem_toFinset]

theorem componentImage_card_le {A V : Type*} [Fintype A] [DecidableEq V]
    (P : SimpleGraph A) (g : A → V) (c : P.ConnectedComponent) :
    (componentImage P g c).card ≤ Fintype.card A := by
  classical
  exact Finset.card_image_le.trans (Finset.card_le_univ _)

theorem componentImage_connected {A V : Type*} [Fintype A] [DecidableEq V]
    (P : SimpleGraph A) (Q : SimpleGraph V) (g : P.Copy Q) (c : P.ConnectedComponent) :
    (Q.induce (componentImage P g c : Set V)).Connected := by
  classical
  let h : c.toSimpleGraph →g Q.induce (componentImage P g c : Set V) := {
    toFun := fun x => ⟨g x.val, (mem_componentImage P g c _).mpr ⟨x.val, x.property, rfl⟩⟩
    map_rel' := fun hadj => g.toHom.map_adj hadj }
  have hsurj : Function.Surjective h := by
    intro v
    obtain ⟨x, hx, heq⟩ := (mem_componentImage P g c v.val).mp v.property
    exact ⟨⟨x, hx⟩, Subtype.ext heq⟩
  exact SimpleGraph.Connected.map h hsurj c.connected_toSimpleGraph

theorem labels_injective_on_component {A V C : Type*} [Fintype A] [DecidableEq V]
    (P : SimpleGraph A) (Q : SimpleGraph V) (g : P.Copy Q) (c : P.ConnectedComponent)
    (label : V → C) (hlabel : Set.InjOn label (componentImage P g c : Set V)) :
    Set.InjOn (label ∘ g) c.supp := by
  intro x hx z hz heq
  apply g.injective
  exact hlabel ((mem_componentImage P g c _).mpr ⟨x, hx, rfl⟩)
    ((mem_componentImage P g c _).mpr ⟨z, hz, rfl⟩) heq

end Erdos911
