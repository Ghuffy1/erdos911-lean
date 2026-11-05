import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.Option

namespace Erdos911

def weightedMean {Ω : Type*} [Fintype Ω] (p f : Ω → ℝ) : ℝ :=
  ∑ ω, p ω * f ω

theorem weightedMean_mono {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    weightedMean p f ≤ weightedMean p g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (hp ω))

theorem weightedMean_add {Ω : Type*} [Fintype Ω] (p f g : Ω → ℝ) :
    weightedMean p (fun ω => f ω + g ω) = weightedMean p f + weightedMean p g := by
  simp [weightedMean, mul_add, Finset.sum_add_distrib]

theorem weightedMean_const {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (c : ℝ) :
    weightedMean p (fun _ => c) = c * ∑ ω, p ω := by
  simp [weightedMean, Finset.mul_sum, mul_comm]

theorem weightedMean_const_mul {Ω : Type*} [Fintype Ω] (p f : Ω → ℝ) (c : ℝ) :
    weightedMean p (fun ω => c * f ω) = c * weightedMean p f := by
  simp [weightedMean, Finset.mul_sum, mul_left_comm]

theorem weightedMean_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : Ω → ℝ) (f : ι → Ω → ℝ) :
    weightedMean p (fun ω => ∑ i, f i ω) = ∑ i, weightedMean p (f i) := by
  simp only [weightedMean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem weightedMean_div {Ω : Type*} [Fintype Ω] (p f : Ω → ℝ) (c : ℝ) :
    weightedMean p (fun ω => f ω / c) = weightedMean p f / c := by
  simp [weightedMean, div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem weightedMean_pos {Ω : Type*} [Fintype Ω] (p f : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp_sum : ∑ ω, p ω = 1) (hf : ∀ ω, 0 < f ω) :
    0 < weightedMean p f := by
  have hpsum : 0 < ∑ ω, p ω := by rw [hp_sum]; norm_num
  obtain ⟨ω, hωmem, hω⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun ω _ => hp ω)).mp hpsum
  exact Finset.sum_pos' (fun ω _ => mul_nonneg (hp ω) (hf ω).le)
    ⟨ω, hωmem, mul_pos hω (hf ω)⟩

/-- Weighted Hölder in normalized form, with a spare constant factor absorbing
any unused exponent weight. This form will be applied one coordinate at a time. -/
theorem weighted_holder_normalized {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : Ω → ℝ) (w : ι → ℝ) (f : ι → Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp_sum : ∑ ω, p ω = 1)
    (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i ≤ 1)
    (hf : ∀ i ω, 0 ≤ f i ω) (hmean : ∀ i, weightedMean p (f i) ≤ 1) :
    weightedMean p (fun ω => ∏ i, (f i ω) ^ (w i)) ≤ 1 := by
  classical
  let weights : Option ι → ℝ := fun i =>
    match i with
    | none => 1 - ∑ j, w j
    | some j => w j
  let values : Ω → Option ι → ℝ := fun ω i =>
    match i with
    | none => 1
    | some j => f j ω
  have hweights : ∀ i ∈ (Finset.univ : Finset (Option ι)), 0 ≤ weights i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hw_sum
    | some i => exact hw i
  have hweights_sum : ∑ i, weights i = 1 := by
    simp [weights, Fintype.sum_option]
  have hvalues : ∀ ω i, 0 ≤ values ω i := by
    intro ω i
    cases i with
    | none => exact zero_le_one
    | some i => exact hf i ω
  have hpoint : ∀ ω, (∏ i, (f i ω) ^ (w i)) ≤
      (1 - ∑ i, w i) + ∑ i, w i * f i ω := by
    intro ω
    have h := Real.geom_mean_le_arith_mean_weighted Finset.univ weights (values ω)
      hweights hweights_sum (fun i _ => hvalues ω i)
    simpa [weights, values, Fintype.prod_option, Fintype.sum_option] using h
  calc
    weightedMean p (fun ω => ∏ i, (f i ω) ^ (w i)) ≤
        weightedMean p (fun ω => (1 - ∑ i, w i) + ∑ i, w i * f i ω) :=
      weightedMean_mono p hp hpoint
    _ = (1 - ∑ i, w i) + ∑ i, w i * weightedMean p (f i) := by
      rw [weightedMean_add, weightedMean_const, weightedMean_sum]
      simp_rw [weightedMean_const_mul]
      rw [hp_sum, mul_one]
    _ ≤ (1 - ∑ i, w i) + ∑ i, w i := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      simpa using mul_le_mul_of_nonneg_left (hmean i) (hw i)
    _ = 1 := by ring

/-- Finite weighted Hölder with an exponent budget at most one. Positivity is
sufficient for all later applications, whose factors are exponentials. -/
theorem weighted_holder {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : Ω → ℝ) (w : ι → ℝ) (f : ι → Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp_sum : ∑ ω, p ω = 1)
    (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i ≤ 1)
    (hf : ∀ i ω, 0 < f i ω) :
    weightedMean p (fun ω => ∏ i, (f i ω) ^ (w i)) ≤
      ∏ i, (weightedMean p (f i)) ^ (w i) := by
  classical
  let a : ι → ℝ := fun i => weightedMean p (f i)
  have ha : ∀ i, 0 < a i := fun i => weightedMean_pos p (f i) hp hp_sum (hf i)
  let g : ι → Ω → ℝ := fun i ω => f i ω / a i
  have hg : ∀ i ω, 0 ≤ g i ω := fun i ω => (div_pos (hf i ω) (ha i)).le
  have hgmean : ∀ i, weightedMean p (g i) ≤ 1 := by
    intro i
    change weightedMean p (fun ω => f i ω / a i) ≤ 1
    rw [weightedMean_div]
    exact le_of_eq (div_self (ha i).ne')
  have hnormalized := weighted_holder_normalized p w g hp hp_sum hw hw_sum hg hgmean
  let K : ℝ := ∏ i, (a i) ^ (w i)
  have hK : 0 < K := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (ha i) _
  have hpoint : ∀ ω, (∏ i, (g i ω) ^ (w i)) = (∏ i, (f i ω) ^ (w i)) / K := by
    intro ω
    dsimp [g, K]
    simp_rw [Real.div_rpow (hf _ _).le (ha _).le]
    rw [Finset.prod_div_distrib]
  simp_rw [hpoint] at hnormalized
  rw [weightedMean_div] at hnormalized
  exact (div_le_one hK).mp hnormalized

/-- Constant factors need no share of the exponent budget. This is the
one-coordinate inequality used when only a subset of factors reads a variable. -/
theorem weighted_holder_effective {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (p : Ω → ℝ) (w : ι → ℝ) (f : ι → Ω → ℝ) (S : Finset ι)
    (hp : ∀ ω, 0 ≤ p ω) (hp_sum : ∑ ω, p ω = 1)
    (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i ∈ S, w i ≤ 1)
    (hf : ∀ i ω, 0 < f i ω)
    (hconstant : ∀ i ∉ S, ∀ ω ω', f i ω = f i ω') :
    weightedMean p (fun ω => ∏ i, (f i ω) ^ (w i)) ≤
      ∏ i, (weightedMean p (f i)) ^ (w i) := by
  classical
  let a : ι → ℝ := fun i => weightedMean p (f i)
  have ha : ∀ i, 0 < a i := fun i => weightedMean_pos p (f i) hp hp_sum (hf i)
  let g : ι → Ω → ℝ := fun i ω => f i ω / a i
  let v : ι → ℝ := fun i => if i ∈ S then w i else 0
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    dsimp [v]
    split_ifs <;> simp_all
  have hv_sum : ∑ i, v i ≤ 1 := by
    simpa [v, Finset.sum_ite] using hw_sum
  have hg : ∀ i ω, 0 ≤ g i ω := fun i ω => (div_pos (hf i ω) (ha i)).le
  have hgmean : ∀ i, weightedMean p (g i) ≤ 1 := by
    intro i
    change weightedMean p (fun ω => f i ω / a i) ≤ 1
    rw [weightedMean_div]
    exact le_of_eq (div_self (ha i).ne')
  have hgone : ∀ i ∉ S, ∀ ω, g i ω = 1 := by
    intro i hi ω
    have hfun : f i = fun _ => f i ω := funext (fun ω' => hconstant i hi ω' ω)
    have hai : a i = f i ω := by
      dsimp [a]
      rw [hfun, weightedMean_const, hp_sum, mul_one]
    dsimp [g]
    rw [hai, div_self (hf i ω).ne']
  have hnormalized := weighted_holder_normalized p v g hp hp_sum hv hv_sum hg hgmean
  have hproduct : (fun ω => ∏ i, (g i ω) ^ (v i)) =
      (fun ω => ∏ i, (g i ω) ^ (w i)) := by
    funext ω
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · simp [v, hi]
    · simp [v, hi, hgone i hi ω]
  rw [hproduct] at hnormalized
  let K : ℝ := ∏ i, (a i) ^ (w i)
  have hK : 0 < K := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (ha i) _
  have hpoint : ∀ ω, (∏ i, (g i ω) ^ (w i)) = (∏ i, (f i ω) ^ (w i)) / K := by
    intro ω
    dsimp [g, K]
    simp_rw [Real.div_rpow (hf _ _).le (ha _).le]
    rw [Finset.prod_div_distrib]
  simp_rw [hpoint] at hnormalized
  rw [weightedMean_div] at hnormalized
  exact (div_le_one hK).mp hnormalized

end Erdos911
