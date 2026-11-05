import Erdos911.CandidateSampling

open MeasureTheory

namespace Erdos911

theorem tested_role_is_large (a p : ℝ) (u d : ℕ) (hp : 0 < p)
    (haccuracy : |a - p * u| ≤ p * d / 16) (htest : p * d / 3 ≤ a) :
    (d : ℝ) / 4 ≤ u := by
  apply (mul_le_mul_iff_right₀ hp).mp
  have h := (abs_le.mp haccuracy).2
  have hpd : 0 ≤ p * d := by positivity
  nlinarith

theorem large_role_is_tested (a p : ℝ) (u d : ℕ) (hp : 0 < p)
    (haccuracy : |a - p * u| ≤ p * d / 16) (hlarge : (d : ℝ) / 2 ≤ u) :
    p * d / 3 ≤ a := by
  have h := (abs_le.mp haccuracy).1
  have hscaled := mul_le_mul_of_nonneg_left hlarge hp.le
  have hpd : 0 ≤ p * d := by positivity
  nlinarith

theorem sample_absolute_count_failure {n : ℕ} (U : Finset (Fin n)) (d : ℕ)
    (hU : U.card ≤ d) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    cubeProbability (fun _ => p)
      {ω | p * d / 16 ≤ |sampleCount U ω - p * U.card|} ≤
      2 * Real.exp (-(p * d) / 2048) := by
  have hmean : (∑ j : U, p) ≤ p * d := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    have hcard : (U.card : ℝ) ≤ d := by exact_mod_cast hU
    nlinarith
  have h := sample_count_two_sided (fun _ => p) U (p * d) (1 / 16)
    (fun _ => hp₀) (fun _ => hp₁) hmean (by norm_num) (by norm_num)
  have hsum : (∑ j : U, p) = p * U.card := by simp [mul_comm]
  have hδ : (1 / 16 : ℝ) * (p * d) = p * d / 16 := by ring
  have he : -((1 / 16 : ℝ) ^ 2 * (p * d)) / 8 = -(p * d) / 2048 := by ring
  rw [hsum, hδ, he,
    ← cubeProbability_eq_measureReal (fun _ => p) (fun _ => hp₀) (fun _ => hp₁)] at h
  exact h

theorem candidate_sampling_failure_quarter {n : ℕ} {W : Type*} [DecidableEq W]
    (U : Finset (Fin n)) (N : Fin n → Finset W) (d D : ℕ)
    (hd : 0 < d) (hdD : d ≤ D) (hU : U.card ≤ d) (hlarge : d ≤ 4 * U.card)
    (hN : ∀ j, (N j).card ≤ D)
    (p ε : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    cubeProbability (fun _ => p) (candidateSamplingFailure U N ε) ≤
      (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512) := by
  have hUpos : 0 < U.card := by omega
  apply (candidate_sampling_failure_probability U N D (fun j _ => hN j)
    hUpos p ε hp₀ hp₁ hε₀ hε₁).trans
  have hcard : ((U.card * D : ℕ) : ℝ) ≤ (D * D : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_right D (hU.trans hdD)
  have hquarter : (d : ℝ) / 4 ≤ U.card := by
    have h : (d : ℝ) ≤ 4 * U.card := by exact_mod_cast hlarge
    linarith
  have hexp : Real.exp (-(ε ^ 2 * (p * U.card)) / 128) ≤
      Real.exp (-(ε ^ 2 * (p * d)) / 512) := by
    apply Real.exp_le_exp.mpr
    have hscale := mul_le_mul_of_nonneg_left hquarter
      (mul_nonneg (sq_nonneg ε) hp₀.le)
    nlinarith
  exact mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by positivity)

/-- The adaptive incidence seed controls the sampled high-neighbor count at
every role and all candidate fractions whenever that high-neighbor set is large. -/
theorem exists_adaptive_connected_seed {n : ℕ} {W : Type*} [DecidableEq W]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.Connected)
    (U : Fin n → Finset (Fin n)) (N : Fin n → Finset W) (d D : ℕ)
    (hdpos : 0 < d) (hdD : d ≤ D) (hd : ∀ v, d ≤ G.degree v)
    (hU : ∀ v, (U v).card ≤ d) (hN : ∀ j, (N j).card ≤ D)
    (p ε : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ∃ (ω : Fin n → Bool) (S : Finset (Fin n)),
      (∀ v, ω v = true → v ∈ S) ∧
        (G.induce (S : Set (Fin n))).Connected ∧
          (∀ v ∉ S, 0 < sampleCount (G.neighborFinset v) ω ∧
            |sampleCount (U v) ω - p * (U v).card| ≤ p * d / 16 ∧
            (d ≤ 4 * (U v).card → 0 < sampleCount (U v) ω ∧ ∀ w : W,
              |sampleCount (candidateSlice (U v) N w) ω / sampleCount (U v) ω -
                ((candidateSlice (U v) N w).card : ℝ) / (U v).card| ≤ ε)) ∧
          (S.card : ℝ) ≤ 3 * n * (p + Real.exp (-(p * d)) +
            2 * Real.exp (-(p * d) / 2048) +
            (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512)) := by
  classical
  let E := fun v => {ω : Fin n → Bool | sampleCount (G.neighborFinset v) ω ≤ 0}
  let B := fun v => {ω : Fin n → Bool |
    p * d / 16 ≤ |sampleCount (U v) ω - p * (U v).card|}
  let F := fun v => if d ≤ 4 * (U v).card then candidateSamplingFailure (U v) N ε else ∅
  let A := fun v => E v ∪ (B v ∪ F v)
  let η := Real.exp (-(p * d)) + 2 * Real.exp (-(p * d) / 2048) +
    (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512)
  have hE : ∀ v, cubeProbability (fun _ => p) (E v) ≤ Real.exp (-(p * d)) := by
    intro v
    have heq : E v = {ω : Fin n → Bool | ∀ w ∈ G.neighborFinset v, ω w = false} := by
      ext ω
      exact sampleCount_nonpos_iff (G.neighborFinset v) ω
    rw [heq]
    apply (empty_sample_probability_le p (G.neighborFinset v) hp₀.le hp₁).trans
    apply Real.exp_le_exp.mpr
    have hdegree : (d : ℝ) ≤ (G.neighborFinset v).card := by exact_mod_cast hd v
    nlinarith
  have hB : ∀ v, cubeProbability (fun _ => p) (B v) ≤
      2 * Real.exp (-(p * d) / 2048) :=
    fun v => sample_absolute_count_failure (U v) d (hU v) p hp₀.le hp₁
  have hF : ∀ v, cubeProbability (fun _ => p) (F v) ≤
      (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512) := by
    intro v
    by_cases hlarge : d ≤ 4 * (U v).card
    · simpa only [F, ite_eq_left hlarge] using
        candidate_sampling_failure_quarter (U v) N d D hdpos hdD (hU v) hlarge
          hN p ε hp₀ hp₁ hε₀ hε₁
    · simp only [F, ite_eq_right hlarge, cubeProbability_empty]
      positivity
  have hA : ∀ v, cubeProbability (fun _ => p) (A v) ≤ η := by
    intro v
    have h₁ := cubeProbability_union_le (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)
      (E v) (B v ∪ F v)
    have h₂ := cubeProbability_union_le (fun _ => p) (fun _ => hp₀.le) (fun _ => hp₁)
      (B v) (F v)
    dsimp only [A, η]
    linarith [hE v, hB v, hF v]
  have hfailure : ∀ v ω, (∀ w ∈ G.neighborFinset v, ω w = false) → ω ∈ A v := by
    intro v ω h
    exact Or.inl ((sampleCount_nonpos_iff (G.neighborFinset v) ω).mpr h)
  obtain ⟨ω, S, hsample, hpass, _, hconn, hsize⟩ := exists_connected_repair_seed G hG
    (fun _ => p) A (fun _ => η) (fun _ => hp₀.le) (fun _ => hp₁) hA hfailure
  refine ⟨ω, S, hsample, hconn, ?_, ?_⟩
  · intro v hv
    have hn := hpass v hv
    refine ⟨lt_of_not_ge (fun h => hn (Or.inl h)), ?_, ?_⟩
    · exact (lt_of_not_ge (fun h => hn (Or.inr (Or.inl h)))).le
    · intro hlarge
      apply candidate_sampling_success (U v) N ε hε₀ ω
      intro hbad
      apply hn
      exact Or.inr (Or.inr (by simpa only [F, ite_eq_left hlarge] using hbad))
  · simpa [η, mul_add, mul_assoc, add_assoc] using hsize

theorem adaptive_failure_budget (d D : ℕ) (hd : 0 < d) (hD : d ≤ D)
    (p ε : ℝ) (hp : 0 ≤ p) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hsample : 4 * Real.log ((D : ℝ) + 1) ≤ ε ^ 2 * (p * d) / 512) :
    Real.exp (-(p * d)) + 2 * Real.exp (-(p * d) / 2048) +
      (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512) ≤
        4 / (d : ℝ) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hDreal : (d : ℝ) ≤ D := by exact_mod_cast hD
  have hpd : 0 ≤ p * d := by positivity
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hεsq hpd
  have hlog : Real.log ((D : ℝ) + 1) ≤ (p * d) / 2048 := by nlinarith
  have htail : Real.exp (-(p * d) / 2048) ≤ 1 / (d : ℝ) := by
    calc
      Real.exp (-(p * d) / 2048) ≤ Real.exp (-Real.log ((D : ℝ) + 1)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = 1 / ((D : ℝ) + 1) := by rw [Real.exp_neg, Real.exp_log hbase, one_div]
      _ ≤ 1 / (d : ℝ) := by
        apply (div_le_div_iff₀ hbase hdreal).mpr
        nlinarith
  have hnone : Real.exp (-(p * d)) ≤ 1 / (d : ℝ) := by
    apply le_trans _ htail
    apply Real.exp_le_exp.mpr
    linarith
  have hsample' : 4 * Real.log ((D : ℝ) + 1) ≤ ε ^ 2 * ((p / 4) * d) / 128 := by
    nlinarith
  have hfrac := candidate_failure_budget d D hd hD (p / 4) ε hsample'
  have he : -(ε ^ 2 * ((p / 4) * d)) / 128 = -(ε ^ 2 * (p * d)) / 512 := by ring
  rw [he] at hfrac
  calc
    Real.exp (-(p * d)) + 2 * Real.exp (-(p * d) / 2048) +
        (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512) ≤
        1 / (d : ℝ) + 2 * (1 / (d : ℝ)) + 1 / (d : ℝ) :=
      add_le_add (add_le_add hnone (mul_le_mul_of_nonneg_left htail (by norm_num))) hfrac
    _ = 4 / (d : ℝ) := by ring

end Erdos911
