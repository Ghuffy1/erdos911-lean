import Erdos911.IncidenceHostPruning

namespace Erdos911

theorem incidenceRightCutoff_bounds (M : ℝ) (d : ℕ) (hM : 1 ≤ M) (hd : 1 ≤ d) :
    32 * M * (d : ℝ) ^ 2 ≤ incidenceRightCutoff M d ∧
      (incidenceRightCutoff M d : ℝ) ≤ 64 * M * (d : ℝ) ^ 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : (1 : ℝ) ≤ M * d * d :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hM hdR) hdR
  have hlo := Nat.le_ceil (32 * M * d * d)
  have hhi := (Nat.ceil_lt_add_one (show 0 ≤ 32 * M * d * d by positivity)).le
  change 32 * M * (d : ℝ) ^ 2 ≤ (Nat.ceil (32 * M * d * d) : ℝ) ∧
    (Nat.ceil (32 * M * d * d) : ℝ) ≤ 64 * M * (d : ℝ) ^ 2
  constructor <;> nlinarith only [hlo, hhi, hbase]

/-- A polynomial target-degree bound gives a fixed polynomial global
host cutoff, independently of the local right-side cutoff. -/
theorem incidence_host_parameters_uniform (B : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀,
      d ≤ nearRegularHostCutoff M d (d ^ B) ∧
      nearRegularHostCutoff M d (d ^ B) ≤ d ^ (B + 2) ∧
      d ^ B ≤ nearRegularHostCutoff M d (d ^ B) ∧
      32 * M * (d : ℝ) ^ 2 ≤ incidenceRightCutoff M d ∧
      (incidenceRightCutoff M d : ℝ) ≤ 64 * M * (d : ℝ) ^ 2 := by
  refine ⟨max 1 (Nat.ceil (32 * M)), ?_⟩
  intro d hd
  have hd1 : 1 ≤ d := (le_max_left _ _).trans hd
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdelta : 1 ≤ d ^ B := one_le_pow₀ hd1
  obtain ⟨hdD, hlo, hhi⟩ := nearRegularHostCutoff_bounds M d (d ^ B) hM hd1 hdelta
  have hMbound : 32 * M ≤ (d : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hd)
  have hDpow : (nearRegularHostCutoff M d (d ^ B) : ℝ) ≤ (d : ℝ) ^ (B + 2) := by
    have h := mul_le_mul_of_nonneg_right hMbound (show 0 ≤ (d : ℝ) * (d : ℝ) ^ B by positivity)
    have hhi' : (nearRegularHostCutoff M d (d ^ B) : ℝ) ≤ 32 * M * d * (d : ℝ) ^ B := by
      simpa only [Nat.cast_pow] using hhi
    rw [pow_add]
    nlinarith only [h, hhi']
  have hfactor : (1 : ℝ) ≤ 16 * M * d := by
    have h := one_le_mul_of_one_le_of_one_le hM hdR
    linarith only [h]
  have hdeltaD : d ^ B ≤ nearRegularHostCutoff M d (d ^ B) := by
    have h := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg (α := ℝ) (d ^ B))
    have hreal : ((d ^ B : ℕ) : ℝ) ≤ nearRegularHostCutoff M d (d ^ B) := by nlinarith only [h, hlo]
    exact_mod_cast hreal
  obtain ⟨hPlo, hPhi⟩ := incidenceRightCutoff_bounds M d hM hd1
  exact ⟨hdD, by exact_mod_cast hDpow, hdeltaD, hPlo, hPhi⟩

end Erdos911
