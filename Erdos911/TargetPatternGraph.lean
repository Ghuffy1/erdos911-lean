import Erdos911.CheapBlockSelection
import Erdos911.CopyImages
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace Erdos911

/-- Each retained row spans a clique on its left pattern. -/
def patternCliqueGraph {A R : Type*} (T : R → Finset A) (U : Finset R) : SimpleGraph A where
  Adj x z := x ≠ z ∧ ∃ y ∈ U, x ∈ T y ∧ z ∈ T y
  symm.symm _ _ h := ⟨h.1.symm, by obtain ⟨y, hy, hx, hz⟩ := h.2; exact ⟨y, hy, hz, hx⟩⟩
  loopless.irrefl _ h := h.1 rfl

theorem patternCliqueGraph_row_reachable {A R : Type*}
    (T : R → Finset A) (U : Finset R) (y : R) (hy : y ∈ U)
    (x z : A) (hx : x ∈ T y) (hz : z ∈ T y) :
    (patternCliqueGraph T U).Reachable x z := by
  by_cases h : x = z
  · subst z; exact .rfl
  · exact SimpleGraph.Adj.reachable ⟨h, y, hy, hx, hz⟩

theorem patternCliqueGraph_row_component {A R : Type*}
    (T : R → Finset A) (U : Finset R) (y : R) (hy : y ∈ U)
    (x : A) (hx : x ∈ T y) :
    ∀ z ∈ T y, z ∈ ((patternCliqueGraph T U).connectedComponentMk x).supp := by
  intro z hz
  exact SimpleGraph.ConnectedComponent.sound (patternCliqueGraph_row_reachable T U y hy z x hz hx)

/-- The vertices covered by retained patterns form a union of components. -/
theorem patternCliqueGraph_covered_component {A R : Type*}
    (T : R → Finset A) (U : Finset R) (x z : A)
    (hx : ∃ y ∈ U, x ∈ T y) (h : (patternCliqueGraph T U).Reachable x z) :
    ∃ y ∈ U, z ∈ T y := by
  have hp := (SimpleGraph.reachable_iff_reflTransGen x z).mp h
  induction hp with
  | refl => exact hx
  | tail _ hadj _ => obtain ⟨y, hy, _, hz⟩ := hadj.2; exact ⟨y, hy, hz⟩

noncomputable def patternComponentRows {A R : Type*} [Fintype A]
    (T : R → Finset A) (B : Finset R) (P : SimpleGraph A) (c : P.ConnectedComponent) : Finset R := by
  classical
  exact B.filter (fun y => ∀ x ∈ T y, x ∈ c.supp)

theorem patternComponentRows_subset {A R : Type*} [Fintype A]
    (T : R → Finset A) (B : Finset R) (P : SimpleGraph A) (c : P.ConnectedComponent) :
    patternComponentRows T B P c ⊆ B := by
  classical
  exact Finset.filter_subset _ _

theorem patternComponentRows_disjoint {A R : Type*} [Fintype A]
    (T : R → Finset A) (B : Finset R) (P : SimpleGraph A)
    (hne : ∀ y ∈ B, (T y).Nonempty) (c d : P.ConnectedComponent) (hcd : c ≠ d) :
    Disjoint (patternComponentRows T B P c) (patternComponentRows T B P d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y hy hd
  obtain ⟨hyB, hyc⟩ := Finset.mem_filter.mp hy
  obtain ⟨_, hyd⟩ := Finset.mem_filter.mp hd
  obtain ⟨x, hx⟩ := hne y hyB
  exact hcd (SimpleGraph.ConnectedComponent.eq_of_common_vertex (hyc x hx) (hyd x hx))

theorem patternComponentRows_sum_le {A R : Type*} [Fintype A] [Fintype R]
    (T : R → Finset A) (B : Finset R) (P : SimpleGraph A) [Fintype P.ConnectedComponent]
    (hne : ∀ y ∈ B, (T y).Nonempty) :
    (∑ c : P.ConnectedComponent, (patternComponentRows T B P c).card) ≤ B.card := by
  classical
  have heq := Finset.card_biUnion (s := (Finset.univ : Finset P.ConnectedComponent))
    (t := patternComponentRows T B P)
    (fun c _ d _ hcd => patternComponentRows_disjoint T B P hne c d hcd)
  rw [← heq]
  apply Finset.card_le_card
  intro y hy
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hy
  exact patternComponentRows_subset T B P c hc

end Erdos911
