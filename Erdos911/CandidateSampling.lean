import Erdos911.ConnectedSeed
import Erdos911.SampleAccuracy

namespace Erdos911

def candidateSlice {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (w : W) : Finset (Fin n) :=
  U.filter (fun j => w ∈ N j)

def candidatePool {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) : Finset W := U.biUnion N

theorem candidateSlice_subset {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (w : W) : candidateSlice U N w ⊆ U :=
  Finset.filter_subset _ _

theorem candidatePool_card_le {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (D : ℕ)
    (hN : ∀ j ∈ U, (N j).card ≤ D) : (candidatePool U N).card ≤ U.card * D := by
  calc
    (candidatePool U N).card ≤ ∑ j ∈ U, (N j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ U, D := Finset.sum_le_sum hN
    _ = U.card * D := by simp

theorem candidateSlice_empty_of_not_mem {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (w : W)
    (hw : w ∉ candidatePool U N) : candidateSlice U N w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have h := Finset.mem_filter.mp hj
  exact hw (Finset.mem_biUnion.mpr ⟨j, h.1, h.2⟩)

def candidateSamplingFailure {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (ε : ℝ) : Set (Fin n → Bool) :=
  samplingFailure U (candidateSlice U N) (candidatePool U N) ε

/-- Only candidates meeting the actual neighborhood require probability
tests. All remaining candidates have identically zero numerator. -/
theorem candidate_sampling_success {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (ε : ℝ) (hε : 0 ≤ ε)
    (ω : Fin n → Bool) (hgood : ω ∉ candidateSamplingFailure U N ε) :
    0 < sampleCount U ω ∧ ∀ w : W,
      |sampleCount (candidateSlice U N w) ω / sampleCount U ω -
        ((candidateSlice U N w).card : ℝ) / U.card| ≤ ε := by
  have hden : 0 < sampleCount U ω := lt_of_not_ge (fun h => hgood (Or.inl h))
  refine ⟨hden, ?_⟩
  intro w
  by_cases hw : w ∈ candidatePool U N
  · exact le_of_not_gt (fun h => hgood (Or.inr ⟨w, hw, h⟩))
  · rw [candidateSlice_empty_of_not_mem U N w hw]
    simpa [sampleCount] using hε

theorem candidate_sampling_failure_probability {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (D : ℕ)
    (hN : ∀ j ∈ U, (N j).card ≤ D) (hU : 0 < U.card)
    (p ε : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    cubeProbability (fun _ => p) (candidateSamplingFailure U N ε) ≤
      (4 * (U.card * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * U.card)) / 128) := by
  apply (samplingFailure_probability U (candidateSlice U N) (candidatePool U N)
    (fun w _ => candidateSlice_subset U N w) hU p ε hp₀ hp₁ hε₀ hε₁).trans
  have hcard : ((candidatePool U N).card : ℝ) ≤ (U.card * D : ℕ) := by
    exact_mod_cast candidatePool_card_le U N D hN
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- The connected seed used for candidate lists, with an explicit probability
budget and simultaneous accuracy for every possible host candidate. -/
theorem exists_accurate_connected_seed {n : ℕ} {W : Type*} [DecidableEq W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.Connected)
    (N : Fin n → Finset W) (d D : ℕ)
    (hdpos : 0 < d) (hd : ∀ v, d ≤ G.degree v) (hD : ∀ v, G.degree v ≤ D)
    (hN : ∀ j, (N j).card ≤ D)
    (p ε : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ∃ (ω : Fin n → Bool) (S : Finset (Fin n)),
      (∀ v, ω v = true → v ∈ S) ∧
        (G.induce (S : Set (Fin n))).Connected ∧
          (∀ v ∉ S, 0 < sampleCount (G.neighborFinset v) ω ∧ ∀ w : W,
            |sampleCount (candidateSlice (G.neighborFinset v) N w) ω /
                sampleCount (G.neighborFinset v) ω -
              ((candidateSlice (G.neighborFinset v) N w).card : ℝ) / G.degree v| ≤ ε) ∧
            (S.card : ℝ) ≤ 3 * n *
              (p + (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 128)) := by
  classical
  let A := fun v => candidateSamplingFailure (G.neighborFinset v) N ε
  let η : ℝ := (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 128)
  have hA : ∀ v, cubeProbability (fun _ => p) (A v) ≤ η := by
    intro v
    have hvpos : 0 < (G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact hdpos.trans_le (hd v)
    apply (candidate_sampling_failure_probability (G.neighborFinset v) N D
      (fun j _ => hN j) hvpos p ε hp₀ hp₁ hε₀ hε₁).trans
    have hcard : (((G.neighborFinset v).card * D : ℕ) : ℝ) ≤ (D * D : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_right D (hD v)
    have hexp : Real.exp (-(ε ^ 2 * (p * (G.neighborFinset v).card)) / 128) ≤
        Real.exp (-(ε ^ 2 * (p * d)) / 128) := by
      apply Real.exp_le_exp.mpr
      have hdeg : (d : ℝ) ≤ (G.neighborFinset v).card := by exact_mod_cast hd v
      have hscale : 0 ≤ ε ^ 2 * p := mul_nonneg (sq_nonneg ε) hp₀.le
      nlinarith [mul_le_mul_of_nonneg_left hdeg hscale]
    apply mul_le_mul
    · linarith
    · exact hexp
    · positivity
    · positivity
  have hfailure : ∀ v ω, (∀ w ∈ G.neighborFinset v, ω w = false) → ω ∈ A v := by
    intro v ω h
    exact Or.inl ((sampleCount_nonpos_iff (G.neighborFinset v) ω).mpr h)
  obtain ⟨ω, S, hsample, hpass, _, hconn, hsize⟩ := exists_connected_repair_seed G hG
    (fun _ => p) A (fun _ => η) (fun _ => hp₀.le) (fun _ => hp₁) hA hfailure
  refine ⟨ω, S, hsample, hconn, ?_, ?_⟩
  · intro v hv
    simpa only [G.card_neighborFinset_eq_degree] using
      candidate_sampling_success (G.neighborFinset v) N ε hε₀ ω (hpass v hv)
  · simpa [η, mul_add, mul_assoc] using hsize

theorem candidate_failure_budget (d D : ℕ) (hd : 0 < d) (hD : d ≤ D)
    (p ε : ℝ)
    (hsample : 4 * Real.log ((D : ℝ) + 1) ≤ ε ^ 2 * (p * d) / 128) :
    (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 128) ≤
      1 / (d : ℝ) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hDreal : (d : ℝ) ≤ D := by exact_mod_cast hD
  have hDnonneg : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hbase : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hexp : Real.exp (-(ε ^ 2 * (p * d)) / 128) ≤
      1 / ((D : ℝ) + 1) ^ 4 := by
    calc
      Real.exp (-(ε ^ 2 * (p * d)) / 128) ≤
          Real.exp (-(4 * Real.log ((D : ℝ) + 1))) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = 1 / ((D : ℝ) + 1) ^ 4 := by
        have he : Real.exp (4 * Real.log ((D : ℝ) + 1)) = ((D : ℝ) + 1) ^ 4 := by
          simpa only [Nat.cast_ofNat, Real.exp_log hbase] using
            Real.exp_nat_mul (Real.log ((D : ℝ) + 1)) 4
        rw [Real.exp_neg, he, one_div]
  have hpoly : (4 * (D : ℝ) ^ 2 + 1) * (D : ℝ) ≤ ((D : ℝ) + 1) ^ 4 := by
    nlinarith [sq_nonneg ((D : ℝ) ^ 2), sq_nonneg (D : ℝ)]
  have hbudget : (4 * (D : ℝ) ^ 2 + 1) * (d : ℝ) ≤ ((D : ℝ) + 1) ^ 4 := by
    exact (mul_le_mul_of_nonneg_left hDreal (by positivity)).trans hpoly
  calc
    (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 128) ≤
        (4 * (D : ℝ) ^ 2 + 1) / ((D : ℝ) + 1) ^ 4 := by
      convert mul_le_mul_of_nonneg_left hexp (show (0 : ℝ) ≤ 4 * (D : ℝ) ^ 2 + 1 by positivity)
        using 1 <;> push_cast <;> ring
    _ ≤ 1 / (d : ℝ) := by
      apply (div_le_div_iff₀ (pow_pos hbase 4) hdreal).mpr
      simpa only [one_mul] using hbudget

end Erdos911
