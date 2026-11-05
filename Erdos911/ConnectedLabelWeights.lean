import Erdos911.RootedCounting
import Erdos911.ExponentialCoordinateLLL
import Mathlib.Algebra.Ring.GeomSum

namespace Erdos911

noncomputable def smallConnectedSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K : ℕ) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun S => 0 < S.card ∧ S.card ≤ K ∧ (G.induce (S : Set V)).Connected)

theorem mem_smallConnectedSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K : ℕ) (S : Finset V) :
    S ∈ smallConnectedSets G K ↔ 0 < S.card ∧ S.card ≤ K ∧ (G.induce (S : Set V)).Connected := by
  classical
  simp only [smallConnectedSets, Finset.mem_filter, Finset.mem_univ, true_and]

theorem geometric_ninth_tail (K : ℕ) :
    (∑ j ∈ Finset.range K, (1 / 9 : ℝ) ^ (j + 1)) ≤ 1 / 8 := by
  have h := geom_sum_mul_neg (1 / 9 : ℝ) K
  have hp : 0 ≤ (1 / 9 : ℝ) ^ K := by positivity
  have heq : (∑ j ∈ Finset.range K, (1 / 9 : ℝ) ^ (j + 1)) =
      (1 / 9) * ∑ j ∈ Finset.range K, (1 / 9 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  rw [heq]
  nlinarith only [h, hp]

theorem connected_label_weight_term (D j : ℕ) (hD : 2 ≤ D) :
    (D : ℝ) ^ (2 * j) * (1 / ((D : ℝ) + 1)) ^ (4 * (j + 1)) ≤ (1 / 9 : ℝ) ^ (j + 1) := by
  let b : ℝ := D + 1
  have hb : 3 ≤ b := by dsimp only [b]; exact_mod_cast (show 3 ≤ D + 1 by omega)
  have hbp : 0 < b := by linarith
  have hpow : (D : ℝ) ^ (2 * j) ≤ b ^ (2 * (j + 1)) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by dsimp [b]; linarith) _).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have hcoef : b ^ 2 * (1 / b) ^ 4 ≤ (1 / 9 : ℝ) := by
    have heq : b ^ 2 * (1 / b) ^ 4 = 1 / b ^ 2 := by field_simp
    rw [heq]
    apply (div_le_iff₀ (pow_pos hbp _)).mpr
    nlinarith only [hb]
  calc
    _ ≤ b ^ (2 * (j + 1)) * (1 / b) ^ (4 * (j + 1)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (b ^ 2 * (1 / b) ^ 4) ^ (j + 1) := by rw [mul_pow, pow_mul, pow_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hcoef _

/-- The total local-lemma weight of all small connected sets containing
a fixed vertex is at most one eighth, independently of the graph order. -/
theorem connected_label_coordinate_budget {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D K : ℕ)
    (hD : 2 ≤ D) (hmax : ∀ v, G.degree v ≤ D) (v : V) :
    (∑ S ∈ (smallConnectedSets G K).filter (fun S => v ∈ S),
      (1 / ((D : ℝ) + 1)) ^ (4 * S.card)) ≤ 1 / 8 := by
  classical
  let F := (smallConnectedSets G K).filter (fun S => v ∈ S)
  let w : ℕ → ℝ := fun j => (1 / ((D : ℝ) + 1)) ^ (4 * (j + 1))
  have hinfo (S : Finset V) (hS : S ∈ F) :
      0 < S.card ∧ S.card ≤ K ∧ (G.induce (S : Set V)).Connected ∧ v ∈ S := by
    obtain ⟨hS', hv⟩ := Finset.mem_filter.mp hS
    obtain ⟨hpos, hsize, hconn⟩ := (mem_smallConnectedSets G K S).mp hS'
    exact ⟨hpos, hsize, hconn, hv⟩
  have hsum : (∑ S ∈ F, (1 / ((D : ℝ) + 1)) ^ (4 * S.card)) =
      ∑ j ∈ Finset.range K, ((F.filter (fun S => S.card - 1 = j)).card : ℝ) * w j := by
    symm
    calc
      _ = ∑ j ∈ Finset.range K, ∑ _S ∈ F.filter (fun S => S.card - 1 = j), w j := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ S ∈ F, w (S.card - 1) := Finset.sum_fiberwise_of_maps_to'
        (fun S hS => Finset.mem_range.mpr (by have hi := hinfo S hS; omega)) w
      _ = _ := Finset.sum_congr rfl (fun S hS => by
        dsimp only [w]
        rw [Nat.sub_add_cancel (hinfo S hS).1])
  have hfiber (j : ℕ) : (F.filter (fun S => S.card - 1 = j)).card ≤ D ^ (2 * j) := by
    have hsub : F.filter (fun S => S.card - 1 = j) ⊆ rootedConnectedSets G v (j + 1) := by
      intro S hS
      obtain ⟨hF, hcard⟩ := Finset.mem_filter.mp hS
      obtain ⟨hpos, _, hconn, hv⟩ := hinfo S hF
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, by omega, hconn⟩
    have h := (Finset.card_le_card hsub).trans (rooted_connected_set_count G D hmax v (j + 1))
    simpa only [Nat.add_sub_cancel] using h
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ Finset.range K, (D : ℝ) ^ (2 * j) * w j := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (by dsimp [w]; positivity)
      exact_mod_cast hfiber j
    _ ≤ ∑ j ∈ Finset.range K, (1 / 9 : ℝ) ^ (j + 1) :=
      Finset.sum_le_sum (fun j _ => connected_label_weight_term D j hD)
    _ ≤ _ := geometric_ninth_tail K

end Erdos911
