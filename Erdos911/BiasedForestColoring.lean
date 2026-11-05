import Erdos911.HostDegreePruning
import Mathlib.Algebra.Order.Floor.Semiring

namespace Erdos911

/-- The non-entropy terms in the full spanning-forest copy bound. -/
noncomputable def forestCountingError (n r m Δ : ℕ) : ℝ :=
  (r : ℝ) * Real.log ((2 * m : ℝ) / r) + r +
    ((n - r : ℕ) : ℝ) * Real.log ((2 * m : ℝ) / ((n - r : ℕ) : ℝ)) +
      ((n - r : ℕ) : ℝ) * Real.log Δ

theorem copyCount_le_forest_entropy {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (Δ : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) (hhost : 0 < H.edgeFinset.card)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v) :
    (H.copyCount G : ℝ) ≤ Real.exp (componentEntropyMass G +
      forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent)
        H.edgeFinset.card Δ) := by
  have h := graph_forest_entropy_bound G H Δ hΔ hhost hneighbors hedge
  convert h using 1
  unfold forestCountingError
  congr 1
  ring

theorem power_budget_of_log_budget (c L b T : ℝ) (t : ℕ)
    (hc : c ≤ Real.exp L) (hb₀ : 0 < b) (hb₁ : b ≤ 1)
    (hT : T ≤ t) (hbudget : L + T * Real.log b < 0) : c * b ^ t < 1 := by
  have hlog : Real.log b ≤ 0 := Real.log_nonpos hb₀.le hb₁
  have hpower : b ^ t = Real.exp ((t : ℝ) * Real.log b) := by
    rw [Real.exp_nat_mul, Real.exp_log hb₀]
  calc
    c * b ^ t ≤ Real.exp L * b ^ t := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = Real.exp (L + (t : ℝ) * Real.log b) := by rw [hpower, Real.exp_add]
    _ ≤ Real.exp (L + T * Real.log b) :=
      Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonpos_right hT hlog))
    _ < 1 := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hbudget

/-- A finite entropy criterion using the original host for counting and its
degree-pruned subgraph for the biased random coloring. -/
theorem biased_degree_pruned_entropy_coloring {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph U) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hFG : F.IsContained G) (hF : F.Connected) (Δ D : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) (hhost : 0 < H.edgeFinset.card)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v)
    (p q η : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * F.edgeFinset.card / 2) ≤ 1 / 2)
    (hincidence : (Fintype.card U * D ^ (2 * (Fintype.card U - 1)) : ℝ) *
      Real.exp (-p * F.edgeFinset.card / 2) ≤ q)
    (hbase : p * Real.exp (2 * q) ≤ 1)
    (hprune : (2 * H.edgeFinset.card * Δ : ℝ) / ((D + 1 : ℕ) : ℝ) ≤
      η * G.edgeSet.ncard)
    (hbudget : componentEntropyMass G +
      forestCountingError (Fintype.card V) (Nat.card G.ConnectedComponent)
        H.edgeFinset.card Δ +
      ((1 - η) * G.edgeSet.ncard) * (Real.log p + 2 * q) < 0) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  let T : ℝ := (1 - η) * G.edgeSet.ncard
  let t := Nat.ceil T
  have hretain : ∀ f : G.Copy H,
      t ≤ (retainedEdges (degreePrunedGraph H D) (copyRawEdges f)).card := by
    intro f
    apply Nat.ceil_le.mpr
    have h := degreePruned_copy_retention G H f Δ D hΔ
    dsimp only [T]
    linarith
  have hb₀ : 0 < p * Real.exp (2 * q) := mul_pos hp₀ (Real.exp_pos _)
  have hlog : Real.log (p * Real.exp (2 * q)) = Real.log p + 2 * q := by
    rw [Real.log_mul hp₀.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hcount := copyCount_le_forest_entropy G H Δ hΔ hhost hneighbors hedge
  have hpowerbudget := power_budget_of_log_budget (H.copyCount G)
    (componentEntropyMass G + forestCountingError (Fintype.card V)
      (Nat.card G.ConnectedComponent) H.edgeFinset.card Δ)
    (p * Real.exp (2 * q)) T t hcount hb₀ hbase (Nat.le_ceil T)
    (by simpa only [hlog, T] using hbudget)
  exact biased_subgraph_avoiding_coloring G F H (degreePrunedGraph H D)
    (degreePrunedGraph_le H D) hFG hF D (degreePrunedGraph_degree_le H D)
    p q hp₀.le hp₁ hq hhalf hincidence t hretain hbase hpowerbudget

end Erdos911
