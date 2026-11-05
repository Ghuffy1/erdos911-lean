import Erdos911.ComponentRoots
import Erdos911.CopySymmetry
import Mathlib.GroupTheory.Perm.Finite

namespace Erdos911

noncomputable def componentMap {V : Type*} (G : SimpleGraph V)
    (σ : Equiv.Perm G.ConnectedComponent)
    (e : ∀ c : G.ConnectedComponent, G.induce c.supp ≃g G.induce (σ c).supp)
    (v : V) : V :=
  (e (G.connectedComponentMk v) ⟨v, rfl⟩).val

theorem componentMap_apply_mem {V : Type*} (G : SimpleGraph V)
    (σ : Equiv.Perm G.ConnectedComponent)
    (e : ∀ c : G.ConnectedComponent, G.induce c.supp ≃g G.induce (σ c).supp)
    (c : G.ConnectedComponent) (v : c.supp) :
    componentMap G σ e v.val = (e c v).val := by
  have hv : G.connectedComponentMk v.val = c := v.property
  obtain ⟨v, hv⟩ := v
  change G.connectedComponentMk v = c at hv
  subst c
  rfl

theorem componentMap_component {V : Type*} (G : SimpleGraph V)
    (σ : Equiv.Perm G.ConnectedComponent)
    (e : ∀ c : G.ConnectedComponent, G.induce c.supp ≃g G.induce (σ c).supp)
    (v : V) : G.connectedComponentMk (componentMap G σ e v) =
      σ (G.connectedComponentMk v) :=
  (e (G.connectedComponentMk v) ⟨v, rfl⟩).property

theorem componentMap_bijective {V : Type*} (G : SimpleGraph V)
    (σ : Equiv.Perm G.ConnectedComponent)
    (e : ∀ c : G.ConnectedComponent, G.induce c.supp ≃g G.induce (σ c).supp) :
    Function.Bijective (componentMap G σ e) := by
  constructor
  · intro u v huv
    have hc : G.connectedComponentMk u = G.connectedComponentMk v := by
      apply σ.injective
      rw [← componentMap_component G σ e u, ← componentMap_component G σ e v, huv]
    let u' : (G.connectedComponentMk u).supp := ⟨u, rfl⟩
    let v' : (G.connectedComponentMk u).supp := ⟨v, hc.symm⟩
    have hmap : e (G.connectedComponentMk u) u' = e (G.connectedComponentMk u) v' := by
      apply Subtype.ext
      rw [← componentMap_apply_mem G σ e _ u', ← componentMap_apply_mem G σ e _ v']
      exact huv
    exact congrArg Subtype.val ((e (G.connectedComponentMk u)).injective hmap)
  · intro v
    let c := σ.symm (G.connectedComponentMk v)
    have hv : v ∈ (σ c).supp := by
      change G.connectedComponentMk v = σ (σ.symm (G.connectedComponentMk v))
      exact (σ.apply_symm_apply _).symm
    let u : c.supp := (e c).symm ⟨v, hv⟩
    refine ⟨u.val, ?_⟩
    rw [componentMap_apply_mem G σ e c u]
    exact congrArg Subtype.val ((e c).apply_symm_apply ⟨v, hv⟩)

theorem componentMap_adj_iff {V : Type*} (G : SimpleGraph V)
    (σ : Equiv.Perm G.ConnectedComponent)
    (e : ∀ c : G.ConnectedComponent, G.induce c.supp ≃g G.induce (σ c).supp)
    (u v : V) :
    G.Adj (componentMap G σ e u) (componentMap G σ e v) ↔ G.Adj u v := by
  have hsame : G.Adj (componentMap G σ e u) (componentMap G σ e v) →
      G.connectedComponentMk u = G.connectedComponentMk v := by
    intro h
    apply σ.injective
    rw [← componentMap_component G σ e u, ← componentMap_component G σ e v]
    exact SimpleGraph.ConnectedComponent.sound h.reachable
  have hiff (hc : G.connectedComponentMk u = G.connectedComponentMk v) :
      G.Adj (componentMap G σ e u) (componentMap G σ e v) ↔ G.Adj u v := by
    let u' : (G.connectedComponentMk u).supp := ⟨u, rfl⟩
    let v' : (G.connectedComponentMk u).supp := ⟨v, hc.symm⟩
    rw [componentMap_apply_mem G σ e _ u', componentMap_apply_mem G σ e _ v']
    exact (e (G.connectedComponentMk u)).map_rel_iff
  constructor
  · intro h
    exact (hiff (hsame h)).mp h
  · intro h
    exact (hiff (SimpleGraph.ConnectedComponent.sound h.reachable)).mpr h

/-- Permuting connected components through chosen component isomorphisms
gives an automorphism of the whole graph. -/
noncomputable def permuteComponents {V : Type*} (G : SimpleGraph V)
    (σ : Equiv.Perm G.ConnectedComponent)
    (e : ∀ c : G.ConnectedComponent, G.induce c.supp ≃g G.induce (σ c).supp) :
    G ≃g G where
  toEquiv := Equiv.ofBijective (componentMap G σ e) (componentMap_bijective G σ e)
  map_rel_iff' := componentMap_adj_iff G σ e _ _

theorem permuteComponents_component {V : Type*} (G : SimpleGraph V)
    (σ : Equiv.Perm G.ConnectedComponent)
    (e : ∀ c : G.ConnectedComponent, G.induce c.supp ≃g G.induce (σ c).supp)
    (v : V) : G.connectedComponentMk (permuteComponents G σ e v) =
      σ (G.connectedComponentMk v) :=
  componentMap_component G σ e v

end Erdos911
