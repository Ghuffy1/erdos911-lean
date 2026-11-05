import Erdos911.BiasedForestColoring

namespace Erdos911

/-- A numerical bound for the anchored red-copy events. -/
theorem anchored_red_weight_bounds (k a d D : ℕ) (p : ℝ)
    (hk : 0 < k) (hd : 0 < d) (hdk : d ≤ k) (hD : 2 ≤ D)
    (haverage : d * k ≤ 2 * a) (hp : 0 ≤ p)
    (hscale : 16 * Real.log D ≤ p * d) :
    Real.exp (-p * a / 2) ≤ 1 / 2 ∧
      (k * D ^ (2 * (k - 1)) : ℝ) * Real.exp (-p * a / 2) ≤ 1 / d := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hlogtwo : Real.log (2 : ℝ) ≤ Real.log D :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  have havg : (d : ℝ) * k ≤ 2 * a := by exact_mod_cast haverage
  have hscale' := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg k)
  have havg' := mul_le_mul_of_nonneg_left havg hp
  have hred : 4 * (k : ℝ) * Real.log D ≤ p * a / 2 := by nlinarith
  have hhalf : Real.exp (-p * a / 2) ≤ 1 / 2 := by
    have hkl := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 4 * k by linarith) hlog
    calc
      Real.exp (-p * a / 2) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hkpow : k ≤ D ^ k := by
    calc
      k ≤ 2 ^ k := Nat.le_of_lt k.lt_two_pow_self
      _ ≤ D ^ k := Nat.pow_le_pow_left hD k
  have hcount : k * D ^ (2 * (k - 1)) ≤ D ^ (3 * k) := by
    calc
      k * D ^ (2 * (k - 1)) ≤ D ^ k * D ^ (2 * k) := by
        apply Nat.mul_le_mul hkpow
        apply Nat.pow_le_pow_right (by omega)
        omega
      _ = D ^ (3 * k) := by rw [← pow_add]; congr 1; omega
  have hcountExp : (k * D ^ (2 * (k - 1)) : ℝ) ≤
      Real.exp (3 * (k : ℝ) * Real.log D) := by
    have heq : (D : ℝ) ^ (3 * k) = Real.exp (3 * (k : ℝ) * Real.log D) := by
      rw [show 3 * (k : ℝ) * Real.log D = ((3 * k : ℕ) : ℝ) * Real.log D by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log hDpos]
    rw [← heq]
    exact_mod_cast hcount
  have hinv : 1 / (D : ℝ) ^ k ≤ 1 / d :=
    one_div_le_one_div_of_le hdpos (by exact_mod_cast hdk.trans hkpow)
  refine ⟨hhalf, ?_⟩
  calc
    (k * D ^ (2 * (k - 1)) : ℝ) * Real.exp (-p * a / 2) ≤
        Real.exp (3 * (k : ℝ) * Real.log D) * Real.exp (-4 * (k : ℝ) * Real.log D) :=
      mul_le_mul hcountExp (Real.exp_le_exp.mpr (by linarith))
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(k : ℝ) * Real.log D) := by rw [← Real.exp_add]; congr 1; ring
    _ = 1 / (D : ℝ) ^ k := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hDpos, one_div]
    _ ≤ 1 / d := hinv

theorem inverse_degree_color_parameters (d D : ℕ) (p : ℝ)
    (hd : 4 ≤ d) (hD : 2 ≤ D) (hp₀ : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hscale : 16 * Real.log D ≤ p * d) :
    4 * (1 / (d : ℝ)) ≤ p ∧ p * Real.exp (2 * (1 / (d : ℝ))) ≤ 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdreal : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hloghalf : 1 / 2 ≤ Real.log (2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogD : 1 / 2 ≤ Real.log D := hloghalf.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hD))
  have hq : 4 * (1 / (d : ℝ)) ≤ p := by
    rw [mul_one_div, div_le_iff₀ hdpos]
    nlinarith
  have hqhalf : 2 * (1 / (d : ℝ)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ hdpos]
    linarith
  have hehalf : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    norm_num at h
    exact h
  have he : Real.exp (2 * (1 / (d : ℝ))) ≤ 2 :=
    (Real.exp_le_exp.mpr hqhalf).trans hehalf
  refine ⟨hq, ?_⟩
  calc
    p * Real.exp (2 * (1 / (d : ℝ))) ≤ p * 2 := mul_le_mul_of_nonneg_left he hp₀
    _ ≤ 1 := by linarith

/-- Minimum degree alone supplies the red-copy local-lemma conditions.
The component order is unrestricted. -/
theorem minimum_degree_red_conditions {U : Type*} [Fintype U] [DecidableEq U]
    (F : SimpleGraph U) [DecidableRel F.Adj] (hF : F.Connected)
    (d D : ℕ) (p : ℝ) (hd : 4 ≤ d) (hD : 2 ≤ D)
    (hmin : ∀ v, d ≤ F.degree v) (hp₀ : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hscale : 16 * Real.log D ≤ p * d) :
    4 * (1 / (d : ℝ)) ≤ p ∧
      Real.exp (-p * F.edgeFinset.card / 2) ≤ 1 / 2 ∧
      (Fintype.card U * D ^ (2 * (Fintype.card U - 1)) : ℝ) *
        Real.exp (-p * F.edgeFinset.card / 2) ≤ 1 / d ∧
      p * Real.exp (2 * (1 / (d : ℝ))) ≤ 1 := by
  obtain ⟨v⟩ := hF.nonempty
  have hdpos : 0 < d := by omega
  have hk : 0 < Fintype.card U := (hmin v).trans_lt (F.degree_lt_card_verts v) |>.pos
  have hdk : d ≤ Fintype.card U := (hmin v).trans (F.degree_lt_card_verts v).le
  have havg : d * Fintype.card U ≤ 2 * F.edgeFinset.card := by
    calc
      d * Fintype.card U = ∑ _ : U, d := by simp [mul_comm]
      _ ≤ ∑ v, F.degree v := Finset.sum_le_sum (fun v _ => hmin v)
      _ = 2 * F.edgeFinset.card := F.sum_degrees_eq_twice_card_edges
  have hred := anchored_red_weight_bounds (Fintype.card U) F.edgeFinset.card d D p
    hk hdpos hdk hD havg hp₀ hscale
  have hparameters := inverse_degree_color_parameters d D p hd hD hp₀ hp hscale
  exact ⟨hparameters.1, hred.1, hred.2, hparameters.2⟩

end Erdos911
