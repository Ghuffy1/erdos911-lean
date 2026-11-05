import Erdos911.PolynomialEntropyThreshold

namespace Erdos911

theorem polynomial_cutoff_retention (A B d m : ℕ) (e : ℝ)
    (hd : 2 ≤ d) (he : 0 ≤ e) (hm : (m : ℝ) ≤ (d : ℝ) ^ A * e) :
    (2 * m * (d : ℝ) ^ B) / ((d ^ (A + B + 2) + 1 : ℕ) : ℝ) ≤
      (1 / (d : ℝ)) * e := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdenpos : (0 : ℝ) < ((d ^ (A + B + 2) + 1 : ℕ) : ℝ) := by positivity
  have hden : ((d ^ (A + B + 2) + 1 : ℕ) : ℝ) =
      (d : ℝ) ^ A * (d : ℝ) ^ B * (d : ℝ) ^ 2 + 1 := by
    push_cast
    rw [pow_add, pow_add]
  have hmult := mul_le_mul_of_nonneg_right hm
    (by positivity : 0 ≤ 2 * (d : ℝ) ^ B * d)
  have hquad : 2 * (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  have hquadmult := mul_le_mul_of_nonneg_right hquad
    (by positivity : 0 ≤ (d : ℝ) ^ A * (d : ℝ) ^ B * e)
  calc
    (2 * m * (d : ℝ) ^ B) / ((d ^ (A + B + 2) + 1 : ℕ) : ℝ) ≤ e / d := by
      apply (div_le_div_iff₀ hdenpos hdpos).mpr
      rw [hden]
      nlinarith only [hmult, hquadmult, he]
    _ = (1 / (d : ℝ)) * e := by ring

theorem ramsey_host_edges_positive {V W : Type*}
    [Fintype V] [DecidableEq V] [Nonempty V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hpositive : ∀ v, 0 < G.degree v) (hRamsey : RamseyFor G G H) :
    0 < H.edgeFinset.card := by
  obtain ⟨v⟩ := ‹Nonempty V›
  have hnotbot : ¬G.IsContained (⊥ : SimpleGraph W) := by
    rintro ⟨f⟩
    have hzero : G.degree v ≤ 0 := by simpa using f.degree_le v
    exact (not_lt_of_ge hzero) (hpositive v)
  have hcontained : G.IsContained H := (hRamsey H le_rfl).resolve_right (by simpa using hnotbot)
  obtain ⟨f⟩ := hcontained
  exact ((hpositive v).trans_le (f.degree_le v)).trans_le (H.degree_le_card_edgeFinset (f v))

/-- The full low-component-entropy branch, uniformly over the target order.
The maximum degree may be any fixed power of the minimum degree. -/
theorem polynomial_low_entropy_size_bound (A B : ℕ) :
    ∃ C : ℝ, ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) →
      (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      componentEntropyMass G ≤ (G.edgeSet.ncard : ℝ) *
        (Real.log d - Real.log (Real.log d) - C) →
      (d : ℝ) ^ A * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  classical
  let K : ℝ := 16 * (A + B + 2 : ℕ)
  have hK : 1 ≤ K := by dsimp only [K]; norm_cast; omega
  obtain ⟨d₀, hd₀⟩ := eventually_polynomial_entropy_parameters A B K
  refine ⟨Real.log K + 1, d₀, ?_⟩
  intro d hd n G hn hmin hmax hentropy
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨hd4, hlog, hp, herror⟩ := hd₀ d hd
  have hdpos : 0 < d := by omega
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hmin' : ∀ v, d ≤ G.degree v := by
    intro v
    simpa only [G.ncard_neighborSet] using hmin v
  have hmax' : ∀ v, G.degree v ≤ d ^ B := by
    intro v
    simpa only [G.ncard_neighborSet] using hmax v
  have hpositive : ∀ v, 0 < G.degree v := fun v => hdpos.trans_le (hmin' v)
  have he : (0 : ℝ) < G.edgeSet.ncard := by
    have hv := hpositive ⟨0, hn⟩
    have heNat := hv.trans_le (G.degree_le_card_edgeFinset ⟨0, hn⟩)
    rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at heNat
    exact_mod_cast heNat
  let D := d ^ (A + B + 2)
  let p := K * Real.log d / d
  have hD : 2 ≤ D := by
    dsimp only [D]
    calc
      2 ≤ d ^ 1 := by simpa using (show 2 ≤ d by omega)
      _ ≤ d ^ (A + B + 2) := Nat.pow_le_pow_right hdpos (by omega)
  have hp₀ : 0 < p := by dsimp only [p]; positivity
  have hscale : 16 * Real.log D ≤ p * d := by
    have heq : 16 * Real.log D = p * d := by
      dsimp only [D, p, K]
      rw [Nat.cast_pow, Real.log_pow]
      field_simp
    exact heq.le
  have hthreshold := polynomial_entropy_threshold_bound A B d K hdpos hlog hK
  have hstrict : Real.log d - Real.log (Real.log d) - (Real.log K + 1) <
      biasedEntropyThreshold d (d ^ B) (d ^ A) p (1 / d) := by
    dsimp only [p]
    linarith
  have hentropy' : componentEntropyMass G <
      (G.edgeSet.ncard : ℝ) * biasedEntropyThreshold d (d ^ B) (d ^ A) p (1 / d) :=
    hentropy.trans_lt (mul_lt_mul_of_pos_left hstrict he)
  by_contra hsize
  obtain ⟨m, H, hHsize, hRamsey⟩ := sizeRamsey_attained G G
  have hhost := ramsey_host_edges_positive G H hpositive hRamsey
  have hbudget : (H.edgeFinset.card : ℝ) ≤ (d : ℝ) ^ A * G.edgeSet.ncard := by
    rw [H.edgeFinset_card, Set.fintypeCard_eq_ncard, hHsize]
    exact le_of_not_gt hsize
  have hprune : (2 * H.edgeFinset.card * (d ^ B : ℕ) : ℝ) / ((D + 1 : ℕ) : ℝ) ≤
      (1 / (d : ℝ)) * G.edgeSet.ncard := by
    simpa only [D, Nat.cast_pow] using
      polynomial_cutoff_retention A B d H.edgeFinset.card G.edgeSet.ncard (by omega) he.le hbudget
  have hΛ : (1 : ℝ) ≤ (d : ℝ) ^ A := one_le_pow₀ (by exact_mod_cast (show 1 ≤ d by omega))
  have hΔ : 1 ≤ d ^ B := one_le_pow₀ (by omega)
  have hnecessary := ramsey_uniform_component_entropy_lower_bound G H d (d ^ B) D
    hd4 hD hΔ hmin' hmax' hhost hRamsey (d ^ A) p (1 / d) hΛ hp₀ hp hscale hbudget hprune
  exact (not_lt_of_ge hnecessary) hentropy'

end Erdos911
