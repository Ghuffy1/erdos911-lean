import Erdos911.ComponentStatistics
import Erdos911.ClassEntropy
import Erdos911.PolynomialLowEntropy
import Erdos911.RepeatedTypePruning

namespace Erdos911

noncomputable def componentDimensions {V : Type*} [Fintype V] (G : SimpleGraph V)
    (t : ComponentType G) : ℕ × ℕ := (componentOrder G t, componentSize G t)

theorem mem_componentClass {V : Type*} [Fintype V] (G : SimpleGraph V)
    (k a : ℕ) (t : ComponentType G) :
    t ∈ componentClass G k a ↔ componentOrder G t = k ∧ componentSize G t = a := by
  classical
  simp only [componentClass, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exponential bounds for every fixed order-and-size class bound the
entropy of the actual component-isomorphism multiplicities. -/
theorem component_class_entropy_bound {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : ∀ v, 1 ≤ G.degree v)
    (L : ℝ) (hclass : ∀ k a, ((componentClass G k a).card : ℝ) ≤ Real.exp (L * a)) :
    componentEntropyMass G ≤ (L + 3 * Real.log 2) * G.edgeSet.ncard := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  let : Nonempty (ComponentType G) := ⟨componentTypeOf G (G.connectedComponentMk v)⟩
  have hr : 0 < ∑ t : ComponentType G, (componentMultiplicity G t : ℝ) :=
    Finset.sum_pos (fun t _ => by exact_mod_cast component_multiplicity_pos G t) Finset.univ_nonempty
  have hpositive (t : ComponentType G) :
      0 < (componentDimensions G t).1 ∧ 0 < (componentDimensions G t).2 :=
    ⟨componentOrder_pos G t, componentSize_pos G hmin t⟩
  have hclasses (p : ℕ × ℕ) :
      (((Finset.univ : Finset (ComponentType G)).filter
        (fun t => componentDimensions G t = p)).card : ℝ) ≤ Real.exp (L * p.2) := by
    obtain ⟨k, a⟩ := p
    simpa only [componentClass, componentDimensions, Prod.mk.injEq] using hclass k a
  have h := weighted_class_entropy_bound (componentMultiplicity G) (componentDimensions G) L
    hr hpositive hclasses
  have horders : (∑ t : ComponentType G, (componentMultiplicity G t : ℝ) * componentOrder G t) =
      Fintype.card V := by exact_mod_cast component_order_mass G
  have hsizes : (∑ t : ComponentType G, (componentMultiplicity G t : ℝ) * componentSize G t) =
      G.edgeSet.ncard := by exact_mod_cast component_size_mass G
  have hvertices : (Fintype.card V : ℝ) ≤ 2 * G.edgeSet.ncard := by
    have hnat : Fintype.card V ≤ 2 * G.edgeFinset.card := by
      calc
        Fintype.card V = ∑ _ : V, 1 := by simp
        _ ≤ ∑ v, G.degree v := Finset.sum_le_sum (fun v _ => hmin v)
        _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hnat
    exact_mod_cast hnat
  change componentEntropyMass G ≤ L *
    (∑ t : ComponentType G, (componentMultiplicity G t : ℝ) * componentSize G t) +
      Real.log 2 * ((∑ t : ComponentType G, (componentMultiplicity G t : ℝ) * componentOrder G t) +
        ∑ t : ComponentType G, (componentMultiplicity G t : ℝ) * componentSize G t) at h
  rw [horders, hsizes] at h
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  nlinarith only [h, mul_le_mul_of_nonneg_left hvertices hlog]

theorem exists_large_component_class {V : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : ∀ v, 1 ≤ G.degree v)
    (L : ℝ) (hentropy : (L + 3 * Real.log 2) * G.edgeSet.ncard < componentEntropyMass G) :
    ∃ t : ComponentType G, Real.exp (L * componentSize G t) <
      ((componentClass G (componentOrder G t) (componentSize G t)).card : ℝ) := by
  classical
  by_contra hno
  push Not at hno
  have hclasses (k a : ℕ) : ((componentClass G k a).card : ℝ) ≤ Real.exp (L * a) := by
    by_cases hempty : componentClass G k a = ∅
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact (Real.exp_pos _).le
    obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hk, ha⟩ := (mem_componentClass G k a t).mp ht
    simpa only [hk, ha] using hno t
  exact (not_lt_of_ge (component_class_entropy_bound G hmin L hclasses)) hentropy

/-- Any counterexample at a fixed polynomial multiplier supplies an
exponentially large class of distinct component types of equal order and size. -/
theorem polynomial_counterexample_large_class (A B : ℕ) :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) →
      (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      (SimpleGraph.sizeRamsey G G : ℝ) ≤ (d : ℝ) ^ A * G.edgeSet.ncard →
      ∃ t : ComponentType G,
        Real.exp ((componentSize G t : ℝ) * (Real.log d - Real.log (Real.log d) - C)) <
          ((componentClass G (componentOrder G t) (componentSize G t)).card : ℝ) := by
  obtain ⟨C, d₀, hlow⟩ := polynomial_low_entropy_size_bound A B
  refine ⟨C + 3 * Real.log 2, max d₀ 1, ?_⟩
  intro d hd n G hn hmin hmax hcheap
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hd₀ : d₀ ≤ d := (le_max_left d₀ 1).trans hd
  have hd1 : 1 ≤ d := (le_max_right d₀ 1).trans hd
  have hmin1 : ∀ v, 1 ≤ G.degree v := by
    intro v
    simpa only [G.ncard_neighborSet] using hd1.trans (hmin v)
  have hhigh : (G.edgeSet.ncard : ℝ) * (Real.log d - Real.log (Real.log d) - C) <
      componentEntropyMass G := by
    by_contra h
    exact (not_lt_of_ge hcheap) (hlow d hd₀ n G hn hmin hmax (le_of_not_gt h))
  let L := Real.log d - Real.log (Real.log d) - (C + 3 * Real.log 2)
  have hentropy : (L + 3 * Real.log 2) * G.edgeSet.ncard < componentEntropyMass G := by
    dsimp only [L]
    nlinarith only [hhigh]
  obtain ⟨t, ht⟩ := exists_large_component_class G hmin1 L hentropy
  exact ⟨t, by simpa only [L, mul_comm] using ht⟩

end Erdos911
