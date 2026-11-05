import Erdos911.ComponentMultiplicity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential

namespace Erdos911

/-- The total multiplicity times the entropy of its normalized distribution.
This form also defines the value when every multiplicity is zero. -/
noncomputable def multiplicityEntropy {I : Type*} [Fintype I] (t : I → ℕ) : ℝ :=
  (∑ i, (t i : ℝ)) * Real.log (∑ i, (t i : ℝ)) -
    ∑ i, (t i : ℝ) * Real.log (t i : ℝ)

theorem log_factorial_lower_bound (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h := Real.pow_div_factorial_le_exp (n : ℝ) (le_of_lt hnpos) n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n / n.factorial) h
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
  linarith

theorem log_factorial_product_lower_bound {I : Type*} [Fintype I] (t : I → ℕ) :
    (∑ i, (t i : ℝ) * Real.log (t i : ℝ)) - ∑ i, (t i : ℝ) ≤
      Real.log (∏ i, ((t i).factorial : ℝ)) := by
  rw [Real.log_prod (fun i _ => by positivity), ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun i _ => log_factorial_lower_bound (t i))

/-- The multiplicity divisor converts the forest expression into an
exponential whose leading term is the component-type entropy. -/
theorem forest_count_entropy_bound {I : Type*} [Fintype I]
    (t : I → ℕ) (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (ht : ∑ i, t i = r)
    (M D c : ℝ) (hM : 0 < M) (hD : 0 < D) (hc : 0 ≤ c)
    (hcount : c ≤ M ^ r * (M / s) ^ s * D ^ s /
      (∏ i, ((t i).factorial : ℝ))) :
    c ≤ Real.exp (multiplicityEntropy t +
      (r : ℝ) * Real.log (M / r) + r +
        (s : ℝ) * Real.log (M / s) + s * Real.log D) := by
  by_cases hzero : c = 0
  · rw [hzero]
    exact (Real.exp_pos _).le
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hzero)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog := Real.log_le_log hcpos hcount
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have hfac := log_factorial_product_lower_bound t
  have hsum : (∑ i, (t i : ℝ)) = r := by exact_mod_cast ht
  have hentropy : multiplicityEntropy t =
      (r : ℝ) * Real.log r - ∑ i, (t i : ℝ) * Real.log (t i : ℝ) := by
    unfold multiplicityEntropy
    rw [hsum]
  apply (Real.log_le_iff_le_exp hcpos).mp
  rw [Real.log_div hM.ne' hrpos.ne', hentropy]
  rw [hsum] at hfac
  linarith

noncomputable def componentEntropyMass {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ :=
  multiplicityEntropy (componentMultiplicity G)

/-- An edge-count entropy bound for the unlabelled copies of an arbitrary
finite target without isolated vertices. -/
theorem graph_forest_entropy_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D) (hhost : 0 < H.edgeFinset.card)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v) :
    (H.copyCount G : ℝ) ≤ Real.exp (componentEntropyMass G +
      (Nat.card G.ConnectedComponent : ℝ) *
        Real.log ((2 * H.edgeFinset.card : ℝ) / Nat.card G.ConnectedComponent) +
      Nat.card G.ConnectedComponent +
      ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ) *
        Real.log ((2 * H.edgeFinset.card : ℝ) /
          ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ)) +
      ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ) * Real.log D) := by
  classical
  obtain ⟨u, v, huv⟩ := hedge
  have hr : 0 < Nat.card G.ConnectedComponent := by
    let : Fintype G.ConnectedComponent := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨G.connectedComponentMk u⟩
  have hs : 0 < Fintype.card V - Nat.card G.ConnectedComponent :=
    Nat.sub_pos_of_lt (components_lt_vertices_of_adj G ⟨u, v, huv⟩)
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast huv.degree_pos_left.trans_le (hD u)
  exact forest_count_entropy_bound (componentMultiplicity G)
    (Nat.card G.ConnectedComponent) (Fintype.card V - Nat.card G.ConnectedComponent)
    hr hs (component_multiplicity_sum G) (2 * H.edgeFinset.card) D (H.copyCount G)
    (by positivity) hDpos (by positivity)
    (graph_forest_component_bound G H D hD hneighbors ⟨u, v, huv⟩)

end Erdos911
