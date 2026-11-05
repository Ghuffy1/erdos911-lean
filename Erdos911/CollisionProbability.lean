import Erdos911.RepeatedLabels

open MeasureTheory

namespace Erdos911

def collisionThreshold (u k : ℕ) : ℕ := u / k + 1

def excessiveCollisions {V A : Type*} (S : Finset V) (k : ℕ) : Set (V → A) :=
  {f | S.card < k * (collisionIndices (orderedSetLabels S f)).card}

theorem excessiveCollisions_depends {V A : Type*} (S : Finset V) (k : ℕ) :
    DependsOnlyOn (excessiveCollisions (A := A) S k) S := by
  intro f g heq hf
  change S.card < k * (collisionIndices (orderedSetLabels S g)).card
  rw [← orderedSetLabels_eq_of_agree S f g heq]
  exact hf

theorem collisionThreshold_bounds (u k : ℕ) (hu : 0 < u) (hk : 2 ≤ k) :
    collisionThreshold u k ≤ u ∧ u ≤ k * collisionThreshold u k := by
  have hdiv : u / k < u := Nat.div_lt_self hu (by omega)
  have hrem : u % k < k := Nat.mod_lt u (by omega)
  have hsum := Nat.mod_add_div u k
  unfold collisionThreshold
  constructor
  · omega
  · calc
      u = u % k + k * (u / k) := hsum.symm
      _ ≤ k + k * (u / k) := Nat.add_le_add_right hrem.le _
      _ = k * (u / k + 1) := by ring

theorem excessiveCollisions_probability {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (S : Finset V) (K D k : ℕ) (hS : 0 < S.card) (hSK : S.card ≤ K)
    (hD : 2 ≤ D) (hk : 2 ≤ k)
    (hpalette : K * (D + 1) ^ (12 * k) ≤ Fintype.card A) :
    (uniformLabelMeasure V A).real (excessiveCollisions S k) ≤
      (1 / ((D : ℝ) + 1)) ^ (10 * S.card) := by
  classical
  let u := S.card
  let r := collisionThreshold u k
  have hr : r ≤ u := (collisionThreshold_bounds u k hS hk).1
  have hur : u ≤ k * r := (collisionThreshold_bounds u k hS hk).2
  have hsub : excessiveCollisions (A := A) S k ⊆
      orderedSetLabels S ⁻¹' (manyCollisionLabels A u r : Set (Fin u → A)) := by
    intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change u < k * (collisionIndices (orderedSetLabels S f)).card at hf
    have hquot : u / k < (collisionIndices (orderedSetLabels S f)).card := by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mpr
      simpa only [Nat.mul_comm] using hf
    exact Nat.succ_le_iff.mpr hquot
  have hraw := (measureReal_mono hsub).trans_eq
    (uniformLabelMeasure_orderedSetLabels S (manyCollisionLabels A u r : Set (Fin u → A)))
  have hcount := uniformLabelMeasure_many_collisions A u r hr
  have hp : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  let b : ℝ := D + 1
  let t : ℝ := 1 / b
  have hb : 3 ≤ b := by dsimp [b]; exact_mod_cast (show 3 ≤ D + 1 by omega)
  have hbp : 0 < b := by linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := (div_le_one hbp).mpr (by linarith)
  have hpR : (K : ℝ) * b ^ (12 * k) ≤ Fintype.card A := by
    dsimp only [b]
    exact_mod_cast hpalette
  have huK : (u : ℝ) ≤ K := by exact_mod_cast hSK
  have hratio : (u : ℝ) / Fintype.card A ≤ t ^ (12 * k) := by
    dsimp only [t]
    rw [one_div_pow]
    apply (div_le_div_iff₀ hp (pow_pos hbp _)).mpr
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right huK (pow_nonneg hbp.le _)).trans hpR
  have hratpow : ((u : ℝ) / Fintype.card A) ^ r ≤ t ^ (12 * u) := by
    calc
      _ ≤ (t ^ (12 * k)) ^ r := pow_le_pow_left₀ (by positivity) hratio _
      _ = t ^ (12 * k * r) := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_of_le_one ht ht1 (by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 12 hur)
  have hthird : t ≤ 1 / 3 := by
    dsimp only [t]
    exact one_div_le_one_div_of_le (by norm_num) hb
  have hcoef : 2 * t ^ 12 ≤ t ^ 10 := by
    have hsq : 2 * t ^ 2 ≤ 1 := by nlinarith only [ht, hthird]
    calc
      2 * t ^ 12 = (2 * t ^ 2) * t ^ 10 := by ring
      _ ≤ 1 * t ^ 10 := mul_le_mul_of_nonneg_right hsq (pow_nonneg ht _)
      _ = _ := one_mul _
  calc
    _ ≤ (2 : ℝ) ^ u * ((u : ℝ) / Fintype.card A) ^ r := hraw.trans hcount
    _ ≤ (2 : ℝ) ^ u * t ^ (12 * u) := mul_le_mul_of_nonneg_left hratpow (by positivity)
    _ = (2 * t ^ 12) ^ u := by rw [mul_pow, pow_mul]
    _ ≤ (t ^ 10) ^ u := pow_le_pow_left₀ (by positivity) hcoef _
    _ = _ := by rw [pow_mul]

end Erdos911
