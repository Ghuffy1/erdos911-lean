import Erdos911.ComponentPermutations
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators

namespace Erdos911

def fiberPermutation {C T : Type*} (label : C → T)
    (π : ∀ t, Equiv.Perm {c : C // label c = t}) : Equiv.Perm C :=
  Equiv.ofFiberEquiv π

theorem fiberPermutation_apply {C T : Type*} (label : C → T)
    (π : ∀ t, Equiv.Perm {c : C // label c = t}) (t : T) (c : {c : C // label c = t}) :
    fiberPermutation label π c.val = (π t c).val := by
  obtain ⟨c, hc⟩ := c
  subst t
  rfl

theorem fiberPermutation_label {C T : Type*} (label : C → T)
    (π : ∀ t, Equiv.Perm {c : C // label c = t}) (c : C) :
    label (fiberPermutation label π c) = label c :=
  Equiv.ofFiberEquiv_map π c

theorem fiberPermutation_injective {C T : Type*} (label : C → T) :
    Function.Injective (fiberPermutation label) := by
  intro π ρ h
  funext t
  apply Equiv.ext
  intro c
  apply Subtype.ext
  rw [← fiberPermutation_apply label π t c, ← fiberPermutation_apply label ρ t c, h]

noncomputable def componentFiberAutomorphism {V T : Type*} (G : SimpleGraph V)
    (label : G.ConnectedComponent → T)
    (htypes : ∀ c d, label c = label d → Nonempty (G.induce c.supp ≃g G.induce d.supp))
    (π : ∀ t, Equiv.Perm {c : G.ConnectedComponent // label c = t}) : G ≃g G :=
  permuteComponents G (fiberPermutation label π)
    (fun c => Classical.choice (htypes c _ (fiberPermutation_label label π c).symm))

theorem componentFiberAutomorphism_injective {V T : Type*} (G : SimpleGraph V)
    (label : G.ConnectedComponent → T)
    (htypes : ∀ c d, label c = label d → Nonempty (G.induce c.supp ≃g G.induce d.supp)) :
    Function.Injective (componentFiberAutomorphism G label htypes) := by
  intro π ρ h
  apply fiberPermutation_injective label
  apply Equiv.ext
  intro c
  have hc := congrArg (fun a : G ≃g G => G.connectedComponentMk (a c.out)) h
  simp only [componentFiberAutomorphism, permuteComponents_component] at hc
  have hout : G.connectedComponentMk c.out = c := c.out_eq
  rw [hout] at hc
  exact hc

/-- Permutations within any classes of isomorphic components contribute
the product of the multiplicity factorials to the automorphism count. -/
theorem labeled_component_multiplicity_aut_bound {V T : Type*} [Fintype V] [Fintype T]
    (G : SimpleGraph V) (label : G.ConnectedComponent → T)
    (htypes : ∀ c d, label c = label d → Nonempty (G.induce c.supp ≃g G.induce d.supp)) :
    (∏ t : T, (Nat.card {c : G.ConnectedComponent // label c = t}).factorial) ≤
      Nat.card (G ≃g G) := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let : Fintype (G ≃g G) :=
    Fintype.ofInjective (fun a : G ≃g G => (a : V → V)) DFunLike.coe_injective
  have h := Fintype.card_le_of_injective (componentFiberAutomorphism G label htypes)
    (componentFiberAutomorphism_injective G label htypes)
  simpa only [Fintype.card_pi, Fintype.card_perm, Nat.card_eq_fintype_card] using h

def componentTypeSetoid {V : Type*} (G : SimpleGraph V) : Setoid G.ConnectedComponent where
  r c d := Nonempty (G.induce c.supp ≃g G.induce d.supp)
  iseqv := {
    refl := fun _ => ⟨SimpleGraph.Iso.refl⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

def ComponentType {V : Type*} (G : SimpleGraph V) := Quotient (componentTypeSetoid G)

noncomputable instance componentTypeFintype {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Fintype (ComponentType G) :=
  Fintype.ofFinite (Quotient (componentTypeSetoid G))

def componentTypeOf {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent) :
    ComponentType G := Quotient.mk (componentTypeSetoid G) c

theorem componentTypeOf_eq_iff {V : Type*} (G : SimpleGraph V) (c d : G.ConnectedComponent) :
    componentTypeOf G c = componentTypeOf G d ↔
      Nonempty (G.induce c.supp ≃g G.induce d.supp) :=
  ⟨Quotient.exact, fun h => @Quotient.sound _ (componentTypeSetoid G) c d h⟩

noncomputable def componentMultiplicity {V : Type*} (G : SimpleGraph V) (t : ComponentType G) : ℕ :=
  Nat.card {c : G.ConnectedComponent // componentTypeOf G c = t}

/-- The factorial divisor for the actual isomorphism-type multiplicities
of the connected components of a finite graph. -/
theorem component_multiplicity_aut_bound {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∏ t : ComponentType G, (componentMultiplicity G t).factorial) ≤ Nat.card (G ≃g G) := by
  exact labeled_component_multiplicity_aut_bound G (componentTypeOf G)
    (fun c d h => (componentTypeOf_eq_iff G c d).mp h)

theorem component_multiplicity_pos {V : Type*} [Fintype V] (G : SimpleGraph V)
    (t : ComponentType G) : 0 < componentMultiplicity G t := by
  classical
  obtain ⟨c, rfl⟩ := Quotient.exists_rep t
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  unfold componentMultiplicity
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff.mpr ⟨⟨c, rfl⟩⟩

theorem component_multiplicity_sum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∑ t : ComponentType G, componentMultiplicity G t) = Nat.card G.ConnectedComponent := by
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  simpa only [componentMultiplicity, Nat.card_eq_fintype_card, Fintype.card_sigma] using
    Fintype.card_congr (Equiv.sigmaFiberEquiv (componentTypeOf G))

theorem component_factorial_product_pos {V : Type*} [Fintype V] (G : SimpleGraph V) :
    0 < ∏ t : ComponentType G, (componentMultiplicity G t).factorial := by
  exact Finset.prod_pos (fun _ _ => Nat.factorial_pos _)

theorem copyCount_mul_component_factorials_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    H.copyCount G * (∏ t : ComponentType G, (componentMultiplicity G t).factorial) ≤
      Fintype.card (G.Copy H) := by
  exact (Nat.mul_le_mul_left _ (component_multiplicity_aut_bound G)).trans
    (copyCount_mul_aut_le G H)

/-- The full forest bound with the component multiplicity divisor. -/
theorem graph_forest_component_bound {V W : Type*}
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
              (∏ t : ComponentType G, ((componentMultiplicity G t).factorial : ℝ)) := by
  have hprod : (0 : ℝ) <
      ∏ t : ComponentType G, ((componentMultiplicity G t).factorial : ℝ) := by positivity
  apply (le_div_iff₀ hprod).mpr
  calc
    (H.copyCount G : ℝ) *
        (∏ t : ComponentType G, ((componentMultiplicity G t).factorial : ℝ)) ≤
          (Fintype.card (G.Copy H) : ℝ) := by
      exact_mod_cast copyCount_mul_component_factorials_le G H
    _ ≤ _ := graph_forest_copy_bound_edges G H D hD hneighbors hedge

end Erdos911
