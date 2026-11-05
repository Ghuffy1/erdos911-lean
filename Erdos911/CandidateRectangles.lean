import Erdos911.ResidualCodegrees

namespace Erdos911

theorem crossEdges_eq_filter_sum {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : crossEdges G A B = ∑ x ∈ A, (B.filter (G.Adj x)).card := by
  classical
  unfold crossEdges
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter]

/-- A large collection of candidates with many neighbors in U yields a dense
rectangle after deleting the candidate vertices from the opposite side. -/
theorem dense_rectangle_from_candidate_rows {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U A : Finset V) (q : ℕ) (ρ : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ) (hU : 2 * q ≤ U.card) (hA : A.card = q)
    (hrow : ∀ x ∈ A, ρ * U.card + q < ((U.filter (G.Adj x)).card : ℝ)) :
    ∃ B : Finset V, B ⊆ U ∧ B.card = q ∧ Disjoint A B ∧
      ρ * q * q < (crossEdges G A B : ℝ) := by
  classical
  let B := U \ A
  have hBcard : q ≤ B.card := by
    change q ≤ (U \ A).card
    have h := Finset.card_le_card_sdiff_add_card (s := U) (t := A)
    omega
  have hrows : ∀ x ∈ A, ρ * U.card < ((B.filter (G.Adj x)).card : ℝ) := by
    intro x hx
    have heq : B.filter (G.Adj x) = U.filter (G.Adj x) \ A := by
      ext z
      simp [B, and_assoc, and_comm, and_left_comm]
    have hcard := Finset.card_le_card_sdiff_add_card (s := U.filter (G.Adj x)) (t := A)
    have hcardR : ((U.filter (G.Adj x)).card : ℝ) ≤
        ((U.filter (G.Adj x) \ A).card : ℝ) + q := by
      exact_mod_cast (by simpa only [hA] using hcard)
    rw [heq]
    linarith [hrow x hx]
  have hnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  have hsum : (q : ℝ) * (ρ * U.card) < (crossEdges G A B : ℝ) := by
    have h := Finset.sum_lt_sum_of_nonempty hnonempty hrows
    simpa only [crossEdges_eq_filter_sum, Nat.cast_sum, Finset.sum_const, nsmul_eq_mul, hA]
      using h
  have hBbound : (B.card : ℝ) ≤ U.card := by
    exact_mod_cast Finset.card_le_card (show B ⊆ U from Finset.sdiff_subset)
  have hqreal : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hmass : (ρ * q) * B.card < ∑ y ∈ B, ((A.filter (G.Adj y)).card : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hBbound (mul_nonneg hρ hqreal)
    rw [crossEdges_comm] at hsum
    simp only [crossEdges_eq_filter_sum, Nat.cast_sum] at hsum
    nlinarith
  obtain ⟨C, hCB, hC, hsumC⟩ := exists_subset_card_sum_gt B
    (fun y => ((A.filter (G.Adj y)).card : ℝ)) (ρ * q) q hq hBcard hmass
  refine ⟨C, hCB.trans Finset.sdiff_subset, hC, Finset.disjoint_left.mpr ?_, ?_⟩
  · intro x hxA hxC
    exact (Finset.mem_sdiff.mp (hCB hxC)).2 hxA
  · rw [crossEdges_comm]
    simpa only [crossEdges_eq_filter_sum, Nat.cast_sum] using hsumC

theorem candidate_list_card_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U L : Finset V) (q : ℕ) (ρ : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ) (hU : 2 * q ≤ U.card)
    (hnodense : ∀ A B : Finset V, A.card = q → B.card = q →
      Disjoint A B → (crossEdges G A B : ℝ) ≤ ρ * q * q)
    (hrow : ∀ x ∈ L, ρ * U.card + q < ((U.filter (G.Adj x)).card : ℝ)) :
    L.card < q := by
  classical
  by_contra hlarge
  obtain ⟨A, hAL, hA⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hlarge)
  obtain ⟨B, _, hB, hdis, hmass⟩ := dense_rectangle_from_candidate_rows G U A q ρ
    hq hρ hU hA (fun x hx => hrow x (hAL hx))
  exact (not_lt_of_ge (hnodense A B hA hB hdis)) hmass

/-- Fraction form used by the candidate lists determined from a sampled seed. -/
theorem candidate_list_card_lt_of_fraction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U L : Finset V) (q : ℕ) (ρ β : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ) (hU : 2 * q ≤ U.card)
    (hnodense : ∀ A B : Finset V, A.card = q → B.card = q →
      Disjoint A B → (crossEdges G A B : ℝ) ≤ ρ * q * q)
    (hgap : ρ * U.card + q < β * U.card)
    (hrow : ∀ x ∈ L, β ≤ ((U.filter (G.Adj x)).card : ℝ) / U.card) : L.card < q := by
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  apply candidate_list_card_lt G U L q ρ hq hρ hU hnodense
  intro x hx
  exact hgap.trans_le ((le_div_iff₀ hUpos).mp (hrow x hx))

theorem sampled_candidate_list_card_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U L : Finset V)
    (f : V → ℝ) (q : ℕ) (ρ τ ε : ℝ)
    (hq : 0 < q) (hρ : 0 ≤ ρ) (hU : 2 * q ≤ U.card)
    (hnodense : ∀ A B : Finset V, A.card = q → B.card = q →
      Disjoint A B → (crossEdges G A B : ℝ) ≤ ρ * q * q)
    (hgap : ρ * U.card + q < (τ - ε) * U.card)
    (hthreshold : ∀ x ∈ L, τ ≤ f x)
    (haccuracy : ∀ x ∈ L, |f x - ((U.filter (G.Adj x)).card : ℝ) / U.card| ≤ ε) :
    L.card < q := by
  apply candidate_list_card_lt_of_fraction G U L q ρ (τ - ε) hq hρ hU hnodense hgap
  intro x hx
  have h := (abs_le.mp (haccuracy x hx)).2
  linarith [hthreshold x hx]

end Erdos911
