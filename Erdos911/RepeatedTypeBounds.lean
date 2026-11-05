import Erdos911.RepeatedTypePruning
import Erdos911.SeedCountLogBounds

namespace Erdos911

noncomputable def repeatedTypeExponent (k a j D M R : ℕ) : ℝ :=
  ((2 * (k - 1) : ℕ) : ℝ) * Real.log D + (a : ℝ) * Real.log ((M : ℝ) / a) -
    (j : ℝ) * Real.log ((M : ℝ) / ((a : ℝ) * R)) + 2 * a

theorem repeatedTypeCount_le_exp (k a j D M R : ℕ)
    (hD : 0 < D) (hM : 0 < M) (hR : 0 < R) (hja : 2 * j ≤ a) :
    (D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j)) : ℝ) ≤
      Real.exp (repeatedTypeExponent k a j D M R) := by
  have hbin := pair_choose_product_exp_bound M R a j hM hR hja
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have heq : (D : ℝ) ^ (2 * (k - 1)) =
      Real.exp (((2 * (k - 1) : ℕ) : ℝ) * Real.log D) := by
    rw [Real.exp_nat_mul, Real.exp_log hDpos]
  calc
    _ ≤ (D : ℝ) ^ (2 * (k - 1)) * Real.exp
        ((a : ℝ) * Real.log ((M : ℝ) / a) - (j : ℝ) * Real.log ((M : ℝ) / ((a : ℝ) * R)) + 2 * a) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_mul] using hbin) (by positivity)
    _ = _ := by rw [heq, ← Real.exp_add]; congr 1; unfold repeatedTypeExponent; ring

theorem exists_repeated_type_support_of_gap {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (R : ℕ) (hP : BoundedEdgeBlocks P R)
    (k a j D M : ℕ) (hD : ∀ w, H.degree w ≤ D)
    (hM : ∀ S : Finset W, S.card = k → (H.induce (S : Set W)).edgeSet.ncard ≤ M)
    (hDpos : 0 < D) (hMpos : 0 < M) (hR : 0 < R) (hja : 2 * j ≤ a)
    (L ε : ℝ) (hε : 0 < ε)
    (hclass : Real.exp (L * a) ≤ ((componentClass G k a).card : ℝ))
    (hgap : repeatedTypeExponent k a j D M R ≤ L * a + Real.log ε) :
    ∃ t ∈ componentClass G k a, (repeatedBadSupport G H P j t).card ≤ ε * H.edgeFinset.card := by
  classical
  have hnonempty : (componentClass G k a).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.exp_pos (L * a)).trans_le hclass
  obtain ⟨t, ht, hsmall⟩ := exists_repeated_type_small_support_of_bounded G H P R hP
    k a j D M hD hM hnonempty
  have hsmallR : (repeatedBadSupport G H P j t).card * ((componentClass G k a).card : ℝ) ≤
      (H.edgeFinset.card : ℝ) *
        (D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j)) : ℝ) := by
    exact_mod_cast hsmall
  have hcount := repeatedTypeCount_le_exp k a j D M R hDpos hMpos hR hja
  have hexp : Real.exp (repeatedTypeExponent k a j D M R) ≤ ε * Real.exp (L * a) := by
    calc
      _ ≤ Real.exp (L * a + Real.log ε) := Real.exp_le_exp.mpr hgap
      _ = _ := by rw [Real.exp_add, Real.exp_log hε]; ring
  refine ⟨t, ht, (mul_le_mul_iff_of_pos_right (Real.exp_pos (L * a))).mp ?_⟩
  calc
    ((repeatedBadSupport G H P j t).card : ℝ) * Real.exp (L * a) ≤
        (repeatedBadSupport G H P j t).card * ((componentClass G k a).card : ℝ) :=
      mul_le_mul_of_nonneg_left hclass (Nat.cast_nonneg _)
    _ ≤ (H.edgeFinset.card : ℝ) *
        (D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j)) : ℝ) := hsmallR
    _ ≤ (H.edgeFinset.card : ℝ) * Real.exp (repeatedTypeExponent k a j D M R) :=
      mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _)
    _ ≤ (H.edgeFinset.card : ℝ) * (ε * Real.exp (L * a)) :=
      mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
    _ = _ := by ring

theorem repeated_type_exponent_deficit (k a j D M R : ℕ) (x : ℝ)
    (hx : 32768 ≤ Real.log x)
    (hroot : ((2 * (k - 1) : ℕ) : ℝ) * Real.log D ≤ (a : ℝ) * Real.log x / 8192)
    (hsize : Real.log ((M : ℝ) / a) ≤ (1 + 1 / 8192 : ℝ) * Real.log x)
    (hpair : (1 - 1 / 8192 : ℝ) * Real.log x ≤ Real.log ((M : ℝ) / ((a : ℝ) * R)))
    (hj : (a : ℝ) / 2048 ≤ j) :
    repeatedTypeExponent k a j D M R ≤ (1 - 1 / 16384 : ℝ) * a * Real.log x := by
  have hmain := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg (α := ℝ) a)
  have hpenalty : (a : ℝ) / 2048 * ((1 - 1 / 8192 : ℝ) * Real.log x) ≤
      (j : ℝ) * Real.log ((M : ℝ) / ((a : ℝ) * R)) := by
    calc
      _ ≤ (j : ℝ) * ((1 - 1 / 8192 : ℝ) * Real.log x) :=
        mul_le_mul_of_nonneg_right hj (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hpair (Nat.cast_nonneg _)
  have hlarge := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg (α := ℝ) a)
  unfold repeatedTypeExponent
  nlinarith only [hroot, hmain, hpenalty, hlarge]

theorem polynomial_repeated_root_bound (A d k a D : ℕ)
    (hscale : 32768 * A ≤ d) (hlog : 0 ≤ Real.log d)
    (haverage : d * k ≤ 2 * a) (hD : 1 ≤ D) (hDpow : D ≤ d ^ A) :
    ((2 * (k - 1) : ℕ) : ℝ) * Real.log D ≤ (a : ℝ) * Real.log d / 8192 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlogD : Real.log D ≤ (A : ℝ) * Real.log d := by
    calc
      Real.log D ≤ Real.log ((d : ℝ) ^ A) := Real.log_le_log hDpos (by exact_mod_cast hDpow)
      _ = _ := Real.log_pow ..
  have hlogDnonneg : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hexponent : ((2 * (k - 1) : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (show 2 * (k - 1) ≤ 2 * k by omega)
  have hAk : 16384 * A * k ≤ a := by
    have h := Nat.mul_le_mul_right k hscale
    nlinarith only [h, haverage]
  have hAkR : (16384 : ℝ) * A * k ≤ a := by exact_mod_cast hAk
  have hscaled := mul_le_mul_of_nonneg_right hAkR hlog
  calc
    _ ≤ 2 * (k : ℝ) * Real.log D := mul_le_mul_of_nonneg_right hexponent hlogDnonneg
    _ ≤ 2 * (k : ℝ) * ((A : ℝ) * Real.log d) :=
      mul_le_mul_of_nonneg_left hlogD (by positivity)
    _ ≤ _ := by nlinarith only [hscaled]

end Erdos911
