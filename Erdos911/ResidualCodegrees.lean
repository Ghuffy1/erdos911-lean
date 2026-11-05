import Erdos911.FiniteAveraging
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Erdos911

noncomputable def neighbors {V : Type*} [Fintype V] (G : SimpleGraph V)
    (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj x)

noncomputable def crossEdges {V : Type*} (G : SimpleGraph V)
    (A B : Finset V) : ℕ := by
  classical
  exact ∑ x ∈ A, (B.filter (G.Adj x)).card

theorem crossEdges_comm {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    crossEdges G A B = crossEdges G B A := by
  classical
  simp only [crossEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  rw [G.adj_comm]

/-- Large codegrees at q partners produce a dense disjoint q-by-q rectangle.
The threshold `2*q ≤ T` ensures that deleting the partners leaves enough
vertices for the averaging argument. -/
theorem dense_rectangle_of_codegrees_at {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : ℕ) (D T ρ : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ)
    (hT : 2 * (q : ℝ) ≤ T) (hgap : ρ * D < T - q)
    (x : V) (hD : ((neighbors G x).card : ℝ) ≤ D) (A : Finset V) (hA : A.card = q)
    (hcodes : ∀ y ∈ A, T < ((neighbors G x ∩ neighbors G y).card : ℝ)) :
    ∃ B : Finset V, B.card = q ∧ Disjoint A B ∧
      ρ * q * q < (crossEdges G A B : ℝ) := by
  classical
  let B := neighbors G x \ A
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hAnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  have hrow : ∀ y ∈ A, T - q < ((B.filter (G.Adj y)).card : ℝ) := by
    intro y hy
    have hid : B.filter (G.Adj y) = (neighbors G x ∩ neighbors G y) \ A := by
      ext z
      simp [B, neighbors, and_assoc, and_comm]
    have hcard := Finset.card_le_card_sdiff_add_card
      (s := neighbors G x ∩ neighbors G y) (t := A)
    have hcardreal : ((neighbors G x ∩ neighbors G y).card : ℝ) ≤
        (((neighbors G x ∩ neighbors G y) \ A).card : ℝ) + (q : ℝ) := by
      exact_mod_cast (by simpa [hA] using hcard)
    rw [hid]
    linarith [hcodes y hy]
  have hBcard : q ≤ B.card := by
    obtain ⟨y, hy⟩ := hAnonempty
    have hfilter : ((B.filter (G.Adj y)).card : ℝ) ≤ B.card := by
      exact_mod_cast Finset.card_filter_le B (G.Adj y)
    have hsmall : (q : ℝ) < B.card := by linarith [hrow y hy]
    exact_mod_cast hsmall.le
  have hBmax : (B.card : ℝ) ≤ D := by
    have hsub : B ⊆ neighbors G x := Finset.sdiff_subset
    have hcard : (B.card : ℝ) ≤ (neighbors G x).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans hD
  have hsum : (q : ℝ) * (T - q) < (crossEdges G A B : ℝ) := by
    have hstrict := Finset.sum_lt_sum_of_nonempty hAnonempty hrow
    simpa only [Finset.sum_const, nsmul_eq_mul, hA, crossEdges, Nat.cast_sum] using hstrict
  have hbudget : ρ * q * B.card < (crossEdges G A B : ℝ) := by
    have hscale := mul_lt_mul_of_pos_left hgap hqreal
    have hscaleB := mul_le_mul_of_nonneg_left hBmax
      (mul_nonneg hρ hqreal.le)
    nlinarith
  have hsumB : (ρ * q) * B.card <
      ∑ y ∈ B, ((A.filter (G.Adj y)).card : ℝ) := by
    rw [crossEdges_comm] at hbudget
    simpa [crossEdges, Nat.cast_sum] using hbudget
  obtain ⟨C, hCB, hC, hsumC⟩ := exists_subset_card_sum_gt B
    (fun y => ((A.filter (G.Adj y)).card : ℝ)) (ρ * q) q hq hBcard hsumB
  refine ⟨C, hC, Finset.disjoint_left.mpr ?_, ?_⟩
  · intro y hyA hyC
    have hyB := hCB hyC
    exact (Finset.mem_sdiff.mp hyB).2 hyA
  · rw [crossEdges_comm]
    simpa [crossEdges, Nat.cast_sum] using hsumC

theorem dense_rectangle_of_codegrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : ℕ) (D T ρ : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ)
    (hD : ∀ x, ((neighbors G x).card : ℝ) ≤ D)
    (hT : 2 * (q : ℝ) ≤ T) (hgap : ρ * D < T - q)
    (x : V) (A : Finset V) (hA : A.card = q)
    (hcodes : ∀ y ∈ A, T < ((neighbors G x ∩ neighbors G y).card : ℝ)) :
    ∃ B : Finset V, B.card = q ∧ Disjoint A B ∧
      ρ * q * q < (crossEdges G A B : ℝ) := by
  exact dense_rectangle_of_codegrees_at G q D T ρ hq hρ hT hgap x (hD x) A hA hcodes

/-- Corrected residual-codegree conclusion. The rectangular hypothesis is
stated directly as an edge-count bound to avoid rounding density parameters. -/
theorem residual_codegrees_at {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : ℕ) (D T ρ : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ)
    (hT : 2 * (q : ℝ) ≤ T) (hgap : ρ * D < T - q)
    (hnodense : ∀ A B : Finset V, A.card = q → B.card = q →
      Disjoint A B → (crossEdges G A B : ℝ) ≤ ρ * q * q) (x : V)
    (hD : ((neighbors G x).card : ℝ) ≤ D) :
    (Finset.univ.filter fun y => x ≠ y ∧
      T < ((neighbors G x ∩ neighbors G y).card : ℝ)).card < q := by
  classical
  by_contra hlarge
  obtain ⟨A, hAsub, hA⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hlarge)
  have hcodes : ∀ y ∈ A, T < ((neighbors G x ∩ neighbors G y).card : ℝ) := by
    intro y hy
    exact (Finset.mem_filter.mp (hAsub hy)).2.2
  obtain ⟨B, hB, hdis, hdense⟩ :=
    dense_rectangle_of_codegrees_at G q D T ρ hq hρ hT hgap x hD A hA hcodes
  exact (not_lt_of_ge (hnodense A B hA hB hdis)) hdense

theorem residual_codegrees {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (q : ℕ) (D T ρ : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ)
    (hD : ∀ x, ((neighbors G x).card : ℝ) ≤ D)
    (hT : 2 * (q : ℝ) ≤ T) (hgap : ρ * D < T - q)
    (hnodense : ∀ A B : Finset V, A.card = q → B.card = q →
      Disjoint A B → (crossEdges G A B : ℝ) ≤ ρ * q * q) (x : V) :
    (Finset.univ.filter fun y => x ≠ y ∧
      T < ((neighbors G x ∩ neighbors G y).card : ℝ)).card < q := by
  exact residual_codegrees_at G q D T ρ hq hρ hT hgap hnodense x (hD x)

end Erdos911
