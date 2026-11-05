import Erdos911.BernoulliCube

namespace Erdos911

def FunctionDependsOn {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (D : Finset (Fin n)) : Prop :=
  ∀ ω ω', (∀ j ∈ D, ω j = ω' j) → f ω = f ω'

def tailCoordinates {n : ℕ} (D : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun j => j.succ ∈ D

theorem FunctionDependsOn.head_constant {n : ℕ}
    {f : (Fin (n + 1) → Bool) → ℝ} {D : Finset (Fin (n + 1))}
    (hf : FunctionDependsOn f D) (hzero : 0 ∉ D)
    (ω : Fin n → Bool) (b b' : Bool) : f (Fin.cons b ω) = f (Fin.cons b' ω) := by
  apply hf
  intro j hj
  cases j using Fin.cases with
  | zero => exact (hzero hj).elim
  | succ j => rfl

theorem FunctionDependsOn.tail_average {n : ℕ}
    {f : (Fin (n + 1) → Bool) → ℝ} {D : Finset (Fin (n + 1))}
    (hf : FunctionDependsOn f D) (p : ℝ) :
    FunctionDependsOn (fun ω => bernoulliMean p (fun b => f (Fin.cons b ω)))
      (tailCoordinates D) := by
  intro ω ω' heq
  apply congrArg (bernoulliMean p)
  funext b
  apply hf
  intro j hj
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    exact heq j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

/-- Finner's product inequality on a finite Bernoulli cube. Each coordinate
has a total incident exponent weight at most one. -/
theorem cube_finner {κ : Type*} [Fintype κ] :
    ∀ (n : ℕ) (p : Fin n → ℝ) (F : κ → (Fin n → Bool) → ℝ)
      (D : κ → Finset (Fin n)) (w : κ → ℝ),
      (∀ j, 0 ≤ p j) → (∀ j, p j ≤ 1) →
      (∀ i ω, 0 < F i ω) → (∀ i, FunctionDependsOn (F i) (D i)) →
      (∀ i, 0 ≤ w i) →
      (∀ j, ∑ i ∈ Finset.univ.filter (fun i => j ∈ D i), w i ≤ 1) →
        cubeMean p (fun ω => ∏ i, (F i ω) ^ (w i)) ≤
          ∏ i, (cubeMean p (F i)) ^ (w i) := by
  classical
  intro n
  induction n with
  | zero =>
    intro p F D w hp₀ hp₁ hF hD hw hbudget
    rfl
  | succ n ih =>
    intro p F D w hp₀ hp₁ hF hD hw hbudget
    let p' : Fin n → ℝ := fun j => p j.succ
    let D' : κ → Finset (Fin n) := fun i => tailCoordinates (D i)
    let G : κ → (Fin n → Bool) → ℝ :=
      fun i ω => bernoulliMean (p 0) (fun b => F i (Fin.cons b ω))
    have hp'₀ : ∀ j, 0 ≤ p' j := fun j => hp₀ j.succ
    have hp'₁ : ∀ j, p' j ≤ 1 := fun j => hp₁ j.succ
    have hG : ∀ i ω, 0 < G i ω := by
      intro i ω
      exact weightedMean_pos (bernoulliWeight (p 0)) (fun b => F i (Fin.cons b ω))
        (bernoulliWeight_nonneg (hp₀ 0) (hp₁ 0)) (bernoulliWeight_sum _) (fun b => hF _ _)
    have hGdep : ∀ i, FunctionDependsOn (G i) (D' i) :=
      fun i => (hD i).tail_average (p 0)
    have hbudget' : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => j ∈ D' i), w i ≤ 1 := by
      intro j
      simpa only [D', tailCoordinates, Finset.mem_filter, Finset.mem_univ, true_and] using
        hbudget j.succ
    have hstep : ∀ ω : Fin n → Bool,
        bernoulliMean (p 0) (fun b => ∏ i, (F i (Fin.cons b ω)) ^ (w i)) ≤
          ∏ i, (G i ω) ^ (w i) := by
      intro ω
      apply weighted_holder_effective (bernoulliWeight (p 0)) w
        (fun i b => F i (Fin.cons b ω)) (Finset.univ.filter fun i => (0 : Fin (n + 1)) ∈ D i)
        (bernoulliWeight_nonneg (hp₀ 0) (hp₁ 0)) (bernoulliWeight_sum _) hw (hbudget 0)
        (fun i b => hF _ _)
      intro i hi b b'
      apply (hD i).head_constant
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_true_eq_false] using hi
    calc
      cubeMean p (fun ω => ∏ i, (F i ω) ^ (w i)) =
          cubeMean p' (fun ω => bernoulliMean (p 0)
            (fun b => ∏ i, (F i (Fin.cons b ω)) ^ (w i))) := rfl
      _ ≤ cubeMean p' (fun ω => ∏ i, (G i ω) ^ (w i)) :=
        cubeMean_mono p' hp'₀ hp'₁ hstep
      _ ≤ ∏ i, (cubeMean p' (G i)) ^ (w i) :=
        ih p' G D' w hp'₀ hp'₁ hG hGdep hw hbudget'
      _ = ∏ i, (cubeMean p (F i)) ^ (w i) := rfl

end Erdos911
