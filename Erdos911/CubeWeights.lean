import Erdos911.BernoulliCube
import Mathlib.Data.Fintype.BigOperators

namespace Erdos911

def cubeWeight {n : ℕ} (p : Fin n → ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ j, bernoulliWeight (p j) (ω j)

theorem cubeWeight_cons {n : ℕ} (p : Fin (n + 1) → ℝ) (b : Bool) (ω : Fin n → Bool) :
    cubeWeight p (Fin.cons b ω) =
      bernoulliWeight (p 0) b * cubeWeight (fun j => p j.succ) ω := by
  simp [cubeWeight, Fin.prod_univ_succ]

/-- The recursively defined expectation is the usual sum against product
Bernoulli weights. This identifies the cube model used by the read bound. -/
theorem cubeMean_eq_weightedMean {n : ℕ} (p : Fin n → ℝ)
    (f : (Fin n → Bool) → ℝ) : cubeMean p f = weightedMean (cubeWeight p) f := by
  induction n with
  | zero =>
    simp [cubeMean, weightedMean, cubeWeight]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    calc
      cubeMean p f = ∑ ω : Fin n → Bool,
          cubeWeight (fun j => p j.succ) ω *
            bernoulliMean (p 0) (fun b => f (Fin.cons b ω)) := by
        rw [cubeMean_succ, ih]
        rfl
      _ = ∑ ω : Fin n → Bool, ∑ b : Bool,
          bernoulliWeight (p 0) b * cubeWeight (fun j => p j.succ) ω * f (Fin.cons b ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [bernoulliMean, weightedMean, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ∑ b : Bool, ∑ ω : Fin n → Bool,
          bernoulliWeight (p 0) b * cubeWeight (fun j => p j.succ) ω * f (Fin.cons b ω) :=
        Finset.sum_comm
      _ = ∑ pair : Bool × (Fin n → Bool),
          cubeWeight p (Fin.cons pair.1 pair.2) * f (Fin.cons pair.1 pair.2) := by
        rw [Fintype.sum_prod_type]
        simp only [cubeWeight_cons]
      _ = weightedMean (cubeWeight p) f := by
        exact (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
          (fun ω => cubeWeight p ω * f ω)

theorem cubeWeight_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1) (ω : Fin n → Bool) :
    0 ≤ cubeWeight p ω :=
  Finset.prod_nonneg (fun j _ => bernoulliWeight_nonneg (hp₀ j) (hp₁ j) (ω j))

theorem cubeWeight_sum {n : ℕ} (p : Fin n → ℝ) : ∑ ω, cubeWeight p ω = 1 := by
  have h := cubeMean_eq_weightedMean p (fun _ => 1)
  rw [cubeMean_const] at h
  simpa [weightedMean] using h.symm

theorem cubeProbability_eq_sum {n : ℕ} (p : Fin n → ℝ) (A : Set (Fin n → Bool))
    [DecidablePred (· ∈ A)] :
    cubeProbability p A = ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ A), cubeWeight p ω := by
  classical
  rw [cubeProbability, cubeMean_eq_weightedMean, weightedMean, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ A <;> simp [hω]

end Erdos911
