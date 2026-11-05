import Erdos911.FiniteHolder
import Mathlib.Data.Fin.Tuple.Basic

namespace Erdos911

def bernoulliWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def bernoulliMean (p : ℝ) (f : Bool → ℝ) : ℝ := weightedMean (bernoulliWeight p) f

theorem bernoulliWeight_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (b : Bool) :
    0 ≤ bernoulliWeight p b := by cases b <;> simp [bernoulliWeight, hp₀, sub_nonneg.mpr hp₁]

theorem bernoulliWeight_sum (p : ℝ) : ∑ b : Bool, bernoulliWeight p b = 1 := by
  simp [bernoulliWeight]

theorem bernoulliMean_eq (p : ℝ) (f : Bool → ℝ) :
    bernoulliMean p f = p * f true + (1 - p) * f false := by
  simp [bernoulliMean, weightedMean, bernoulliWeight]

theorem bernoulliMean_const (p c : ℝ) : bernoulliMean p (fun _ => c) = c := by
  rw [bernoulliMean, weightedMean_const, bernoulliWeight_sum, mul_one]

noncomputable def cubeMean : {n : ℕ} → (Fin n → ℝ) → ((Fin n → Bool) → ℝ) → ℝ
  | 0, _, f => f (fun i => Fin.elim0 i)
  | n + 1, p, f => cubeMean (fun i : Fin n => p i.succ)
      (fun ω => bernoulliMean (p 0) (fun b => f (Fin.cons b ω)))

@[simp] theorem cubeMean_zero (p : Fin 0 → ℝ) (f : (Fin 0 → Bool) → ℝ) :
    cubeMean p f = f (fun i => Fin.elim0 i) := rfl

@[simp] theorem cubeMean_succ {n : ℕ} (p : Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → Bool) → ℝ) :
    cubeMean p f = cubeMean (fun i : Fin n => p i.succ)
      (fun ω => bernoulliMean (p 0) (fun b => f (Fin.cons b ω))) := rfl

theorem cubeMean_const {n : ℕ} (p : Fin n → ℝ) (c : ℝ) :
    cubeMean p (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cubeMean_succ, bernoulliMean_const, ih]

theorem cubeMean_mono {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1)
    {f g : (Fin n → Bool) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    cubeMean p f ≤ cubeMean p g := by
  induction n with
  | zero => exact hfg _
  | succ n ih =>
    apply ih (fun i => p i.succ) (fun i => hp₀ i.succ) (fun i => hp₁ i.succ)
    intro ω
    exact weightedMean_mono (bernoulliWeight (p 0))
      (bernoulliWeight_nonneg (hp₀ 0) (hp₁ 0)) (fun b => hfg (Fin.cons b ω))

theorem cubeMean_pos {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1)
    {f : (Fin n → Bool) → ℝ} (hf : ∀ ω, 0 < f ω) : 0 < cubeMean p f := by
  induction n with
  | zero => exact hf _
  | succ n ih =>
    apply ih (fun i => p i.succ) (fun i => hp₀ i.succ) (fun i => hp₁ i.succ)
    intro ω
    exact weightedMean_pos (bernoulliWeight (p 0)) (fun b => f (Fin.cons b ω))
      (bernoulliWeight_nonneg (hp₀ 0) (hp₁ 0)) (bernoulliWeight_sum _) (fun b => hf _)

theorem cubeMean_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp₀ : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1)
    {f : (Fin n → Bool) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ cubeMean p f := by
  have h := cubeMean_mono p hp₀ hp₁ (f := fun _ => 0) hf
  simpa only [cubeMean_const] using h

theorem cubeMean_add {n : ℕ} (p : Fin n → ℝ)
    (f g : (Fin n → Bool) → ℝ) :
    cubeMean p (fun ω => f ω + g ω) = cubeMean p f + cubeMean p g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeMean_succ, bernoulliMean, weightedMean_add, ih]

theorem cubeMean_const_mul {n : ℕ} (p : Fin n → ℝ)
    (f : (Fin n → Bool) → ℝ) (c : ℝ) :
    cubeMean p (fun ω => c * f ω) = c * cubeMean p f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeMean_succ, bernoulliMean, weightedMean_const_mul, ih]

theorem cubeMean_sub {n : ℕ} (p : Fin n → ℝ)
    (f g : (Fin n → Bool) → ℝ) :
    cubeMean p (fun ω => f ω - g ω) = cubeMean p f - cubeMean p g := by
  have heq : (fun ω => f ω - g ω) = (fun ω => f ω + (-1) * g ω) := by
    funext ω
    ring
  rw [heq, cubeMean_add, cubeMean_const_mul]
  ring

theorem cubeMean_sum {n : ℕ} {ι : Type*} [Fintype ι] (p : Fin n → ℝ)
    (f : ι → (Fin n → Bool) → ℝ) :
    cubeMean p (fun ω => ∑ i, f i ω) = ∑ i, cubeMean p (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeMean_succ, bernoulliMean, weightedMean_sum, ih]

noncomputable def cubeProbability {n : ℕ} (p : Fin n → ℝ)
    (A : Set (Fin n → Bool)) : ℝ := by
  classical
  exact cubeMean p (A.indicator (fun _ => 1))

end Erdos911
