import Erdos911.QuarterDegreeParameters
import Erdos911.PolynomialLocalRamsey

namespace Erdos911

/-- Uniform superlinear size-Ramsey growth for every fixed polynomial
maximum-degree bound. The local-density hypothesis has been removed. -/
theorem polynomial_size_ramsey_lower_bound (B : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], 0 < Fintype.card V →
      (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ d ^ B) →
      (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  let C := polynomialCoreCoefficient B (B + 2)
  have hC : 1 ≤ C := polynomialCoreCoefficient_pos B (B + 2)
  obtain ⟨q₀, hq₀⟩ := polynomial_local_size_ramsey_lower_bound (B + 1) (20 * M) (2 * (C + 1))
    (by linarith) (by linarith)
  refine ⟨max 25 (max (5 ^ (B + 1)) (max (4 * q₀) (Nat.ceil (8 * M)))), ?_⟩
  intro d hd V _ _ G _ hV hmin hmax
  classical
  have hd25 : 25 ≤ d := (le_max_left _ _).trans hd
  have hdpow : 5 ^ (B + 1) ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hdq₀ : 4 * q₀ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hdMnat : Nat.ceil (8 * M) ≤ d := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hd))
  have hdM : 8 * M ≤ (d : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hdMnat)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdp : (0 : ℝ) < d := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hlogd : 1 ≤ Real.log d := by
    have he : Real.exp 1 ≤ (d : ℝ) := Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ d by omega))
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  let s := Nat.ceil (C * Real.log d)
  have hslo : C * Real.log d ≤ (s : ℝ) := Nat.le_ceil _
  have hsR : (1 : ℝ) ≤ s := by nlinarith only [hslo, hC, hlogd]
  have hsp : (0 : ℝ) < s := by linarith
  have heG : 0 < G.edgeSet.ncard := by
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV
    have hp : 0 < G.degree v := (show 0 < d by omega).trans_le (hmin v)
    have he := hp.trans_le (G.degree_le_card_edgeFinset v)
    simpa only [G.edgeFinset_card, Set.fintypeCard_eq_ncard] using he
  have heGR : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast heG
  rcases dense_core_or_locally_sparse_target G d (d ^ B) (d ^ (B + 2)) s hmin hmax with
    ⟨U, J, hJG, hJmin, hJorder, hmass⟩ | ⟨U, J, hJG, hJmin, hJmax, hJlocal, hmass⟩
  · let : Fintype U := Fintype.ofFinite _
    let : DecidableRel J.Adj := Classical.decRel _
    obtain ⟨f⟩ := hJG
    have heJ : 0 < J.edgeSet.ncard := by
      by_contra h
      have hz : J.edgeSet.ncard = 0 := by omega
      rw [hz, Nat.cast_zero, mul_zero] at hmass
      nlinarith only [hmass, heGR, hsp]
    have hU : 0 < Fintype.card U := by
      by_contra h
      have hz : Fintype.card U = 0 := by omega
      let : IsEmpty U := Fintype.card_eq_zero_iff.mp hz
      have hzJ : J = ⊥ := Subsingleton.elim _ _
      simp only [hzJ, SimpleGraph.edgeSet_bot, Set.ncard_empty] at heJ
      omega
    have hJmax : ∀ v, J.degree v ≤ d ^ B := fun v => (f.degree_le v).trans (hmax (f v))
    have hJmin' : ∀ v, s ≤ J.degree v := by simpa only [SimpleGraph.ncard_neighborSet] using hJmin
    have hsΔ : s ≤ d ^ B := by
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hU
      exact (hJmin' v).trans (hJmax v)
    have hJ := polynomial_component_palette_ramsey B (B + 2) d s (by omega) hslo hsΔ
      J hU hJmin' hJmax hJorder
    have hcoarse : (G.edgeSet.ncard : ℝ) ≤ 8 * (d : ℝ) ^ B * J.edgeSet.ncard := by
      rw [Nat.cast_pow] at hmass
      exact (le_mul_of_one_le_left (Nat.cast_nonneg _) hsR).trans hmass
    have hcoef : 8 * M * (d : ℝ) ^ (B + 1) ≤ (d : ℝ) ^ (B + 3) := by
      have hd2 : 8 * M ≤ (d : ℝ) ^ 2 := by nlinarith only [hdM, hdR]
      have hm := mul_le_mul_of_nonneg_right hd2 (pow_nonneg hdp.le (B + 1))
      have hexp : (d : ℝ) ^ (B + 3) = (d : ℝ) ^ 2 * (d : ℝ) ^ (B + 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hexp]
      exact hm
    have hbudget : (M * d) * G.edgeSet.ncard ≤ (d : ℝ) ^ (B + 3) * J.edgeSet.ncard := by
      calc
        _ ≤ (M * d) * (8 * (d : ℝ) ^ B * J.edgeSet.ncard) :=
          mul_le_mul_of_nonneg_left hcoarse (by positivity)
        _ = (8 * M * (d : ℝ) ^ (B + 1)) * J.edgeSet.ncard := by rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    have hmono : (SimpleGraph.sizeRamsey J J : ℝ) ≤ SimpleGraph.sizeRamsey G G := by
      exact_mod_cast sizeRamsey_mono ⟨f⟩ ⟨f⟩
    exact hbudget.trans_lt (hJ.trans_le hmono)
  · let : Fintype U := Fintype.ofFinite _
    let : DecidableRel J.Adj := Classical.decRel _
    obtain ⟨f⟩ := hJG
    have heJ : 0 < J.edgeSet.ncard := by
      have heJR : (0 : ℝ) < J.edgeSet.ncard := lt_of_lt_of_le (by positivity) hmass
      exact_mod_cast heJR
    have hU : 0 < Fintype.card U := by
      by_contra h
      have hz : Fintype.card U = 0 := by omega
      let : IsEmpty U := Fintype.card_eq_zero_iff.mp hz
      have hzJ : J = ⊥ := Subsingleton.elim _ _
      simp only [hzJ, SimpleGraph.edgeSet_bot, Set.ncard_empty] at heJ
      omega
    obtain ⟨hq, hdq, hpower, hlogs, hceil⟩ := quarter_degree_parameter_bounds B d C hC hd25 hdpow
    have hlocal : ∀ S : Finset U, S.card ≤ (d / 4) ^ (B + 1 + 1) →
        ((J.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ (2 * (C + 1)) * Real.log (d / 4 : ℕ) * S.card := by
      intro S hS
      have hsize : S.card ≤ d ^ (B + 2) := by
        have hpow := Nat.pow_le_pow_left (show d / 4 ≤ d by omega) (B + 2)
        have hS' : S.card ≤ (d / 4) ^ (B + 2) := by simpa only [Nat.add_assoc] using hS
        exact hS'.trans hpow
      exact (hJlocal S hsize).trans (mul_le_mul_of_nonneg_right hceil (Nat.cast_nonneg _))
    have hJ := hq₀ (d / 4) (by omega) U J hU
      (by simpa only [SimpleGraph.ncard_neighborSet] using hJmin)
      (fun v => by
        have hv : J.degree v ≤ d ^ B := by simpa only [SimpleGraph.ncard_neighborSet] using hJmax v
        exact hv.trans hpower) hlocal
    have hbudget : (M * d) * G.edgeSet.ncard ≤ ((20 * M) * (d / 4 : ℕ)) * J.edgeSet.ncard := by
      have hdqR : (d : ℝ) ≤ 5 * (d / 4 : ℕ) := by exact_mod_cast hdq
      have hcoef : (M * d) * 4 ≤ (20 * M) * (d / 4 : ℕ) := by
        have hm := mul_le_mul_of_nonneg_left hdqR hM0
        nlinarith only [hm]
      calc
        _ ≤ (M * d) * (4 * J.edgeSet.ncard) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith only [hmass]
        _ = ((M * d) * 4) * J.edgeSet.ncard := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    have hmono : (SimpleGraph.sizeRamsey J J : ℝ) ≤ SimpleGraph.sizeRamsey G G := by
      exact_mod_cast sizeRamsey_mono ⟨f⟩ ⟨f⟩
    exact hbudget.trans_lt (hJ.trans_le hmono)

end Erdos911
