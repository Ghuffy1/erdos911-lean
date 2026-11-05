import Erdos911.SeedCountLogBounds

namespace Erdos911

def seedEventCountBound (k D s q : ℕ) : ℕ :=
  q * seedAssignmentCountBound k D D s 0

def seedEventSupportBound (k D q t h : ℕ) : ℕ := h * k * q * D ^ t

def seedEventLogCoefficient (A h t : ℕ) (C : ℝ) : ℝ :=
  C * (4 * A + 1) + (t + 1) * A + h + 20

theorem seedEventCountBound_pos (k D s q : ℕ) (hk : 0 < k) (hD : 0 < D) (hq : 0 < q) :
    0 < seedEventCountBound k D s q := by
  unfold seedEventCountBound seedAssignmentCountBound
  positivity

theorem seedEventSupportBound_pos (k D q t h : ℕ)
    (hk : 0 < k) (hD : 0 < D) (hq : 0 < q) (hh : 0 < h) :
    0 < seedEventSupportBound k D q t h := by
  unfold seedEventSupportBound
  positivity

/-- The complete local-lemma logarithm, including event supports, has
a bound uniform over every component order at least d. -/
theorem uniform_seed_event_log_bound (A d k D s q₁ q₂ t h : ℕ) (C : ℝ)
    (hd : 1 ≤ d) (hdk : d ≤ k) (hD : 1 ≤ D) (hDpow : D ≤ d ^ A)
    (hs : s ≤ k) (hC : 0 ≤ C) (hlog : 1 ≤ Real.log d)
    (hseed : (s : ℝ) ≤ C * k * (Real.log d) ^ 2 / d)
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) (hq₁d : q₁ ≤ d) (hq₂d : q₂ ≤ d) (hh : 1 ≤ h) :
    Real.log (8 * (seedEventCountBound k D s q₂ : ℝ) * seedEventSupportBound k D q₁ t h) ≤
      (k : ℝ) / d * (seedEventLogCoefficient A h t C * (Real.log d) ^ 3) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hq₁R : (0 : ℝ) < q₁ := by exact_mod_cast (show 0 < q₁ by omega)
  have hq₂R : (0 : ℝ) < q₂ := by exact_mod_cast (show 0 < q₂ by omega)
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hratio : 1 ≤ (k : ℝ) / d := (one_le_div hdR).mpr (by exact_mod_cast hdk)
  let L := Real.log (d : ℝ)
  let M := (k : ℝ) / d * L ^ 3
  have hL : 1 ≤ L := hlog
  have hLnonneg : 0 ≤ L := by linarith
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL3 : L ^ 2 ≤ L ^ 3 := by nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)]
  have hL3one : 1 ≤ L ^ 3 := le_trans hL (le_trans hL2 hL3)
  have hLM : L ≤ M := calc
    L ≤ L ^ 3 := hL2.trans hL3
    _ ≤ (k : ℝ) / d * L ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (pow_nonneg hLnonneg 3)]
  have hM : 1 ≤ M := hL.trans hLM
  have hs' : (s : ℝ) ≤ (C * L) * k * Real.log d / d := by
    calc
      _ ≤ C * k * (Real.log d) ^ 2 / d := hseed
      _ = _ := by dsimp [L]; ring
  have hcore := uniform_seed_assignment_log_bound_of_log_choices A d k D s 0 (C * L) 0
    hd hdk hD hDpow hs hs' (by norm_num)
  have hsmall : ((A : ℝ) + 2) * L + 4 + C * L * L * (4 * A * L + 1) ≤
      ((A : ℝ) + 6 + C * (4 * A + 1)) * L ^ 3 := by
    have hlinear := mul_le_mul_of_nonneg_left (hL2.trans hL3)
      (show 0 ≤ (A : ℝ) + 2 by positivity)
    have hconstant := mul_le_mul_of_nonneg_left hL3one (show (0 : ℝ) ≤ 4 by norm_num)
    have hinner : 4 * (A : ℝ) * L + 1 ≤ (4 * A + 1) * L := by linarith
    have hquadratic := mul_le_mul_of_nonneg_left hinner (mul_nonneg hC (sq_nonneg L))
    nlinarith only [hlinear, hconstant, hquadratic]
  have hcore' : Real.log (seedAssignmentCountBound k D D s 0 : ℝ) ≤
      M * ((A : ℝ) + 6 + C * (4 * A + 1)) := by
    calc
      _ ≤ (k : ℝ) * (0 + (((A : ℝ) + 2) * L + 4 +
          (C * L) * L * (4 * A * L + 1)) / d) := hcore
      _ = (k : ℝ) / d * (((A : ℝ) + 2) * L + 4 + C * L * L * (4 * A * L + 1)) := by ring
      _ ≤ (k : ℝ) / d * (((A : ℝ) + 6 + C * (4 * A + 1)) * L ^ 3) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by dsimp [M]; ring
  have hlogk : Real.log k ≤ 2 * M := by
    apply (log_order_uniform_bound (d : ℝ) k (by exact_mod_cast hd) (by exact_mod_cast hdk)).trans
    calc
      (k : ℝ) / d * (L + 1) ≤ (k : ℝ) / d * (2 * L ^ 3) :=
        mul_le_mul_of_nonneg_left (by linarith [hL2.trans hL3]) (by positivity)
      _ = 2 * M := by dsimp [M]; ring
  have hlogq₁ : Real.log q₁ ≤ M :=
    (Real.log_le_log hq₁R (by exact_mod_cast hq₁d)).trans hLM
  have hlogq₂ : Real.log q₂ ≤ M :=
    (Real.log_le_log hq₂R (by exact_mod_cast hq₂d)).trans hLM
  have hlogh : Real.log h ≤ (h : ℝ) * M := by
    have hx := Real.log_le_sub_one_of_pos hhR
    have hy := mul_le_mul_of_nonneg_left hM hhR.le
    nlinarith
  have hlogD : (t : ℝ) * Real.log D ≤ (t : ℝ) * A * M := by
    have hx : Real.log D ≤ (A : ℝ) * L := by
      calc
        _ ≤ Real.log ((d : ℝ) ^ A) := Real.log_le_log hDR (by exact_mod_cast hDpow)
        _ = _ := by rw [Real.log_pow]
    apply (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg t)).trans
    have hscaled := mul_le_mul_of_nonneg_left hLM (show 0 ≤ (t : ℝ) * A by positivity)
    simpa only [mul_assoc] using hscaled
  have hlog8 : Real.log (8 : ℝ) ≤ 8 * M := by
    have hx := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
    nlinarith
  have hcorepos : (0 : ℝ) < seedAssignmentCountBound k D D s 0 := by
    have hkpos : 0 < k := by omega
    have hDpos : 0 < D := by omega
    unfold seedAssignmentCountBound
    positivity
  have heq : Real.log (8 * (seedEventCountBound k D s q₂ : ℝ) * seedEventSupportBound k D q₁ t h) =
      Real.log 8 + Real.log q₂ + Real.log (seedAssignmentCountBound k D D s 0 : ℝ) +
        Real.log h + Real.log k + Real.log q₁ + (t : ℝ) * Real.log D := by
    simp only [seedEventCountBound, seedEventSupportBound, Nat.cast_mul, Nat.cast_pow]
    repeat rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    ring
  rw [heq]
  calc
    _ ≤ M * seedEventLogCoefficient A h t C := by
      unfold seedEventLogCoefficient
      nlinarith only [hcore', hlogk, hlogq₁, hlogq₂, hlogh, hlogD, hlog8, hM]
    _ = _ := by dsimp [M, L]; ring

end Erdos911
