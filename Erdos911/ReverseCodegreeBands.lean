import Erdos911.LightIncidenceMass
import Erdos911.EdgeBands

namespace Erdos911

theorem exists_dyadic_enclosure (W : ℝ) (hW : 1 ≤ W) :
    ∃ n : ℕ, W ≤ (2 : ℝ) ^ n ∧ (2 : ℝ) ^ n ≤ 2 * W := by
  have hex : ∃ n : ℕ, W ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := exists_nat_gt W
    have hp : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.le_of_lt n.lt_two_pow_self
    exact ⟨n, hn.le.trans hp⟩
  let n := Nat.find hex
  have hlo : W ≤ (2 : ℝ) ^ n := Nat.find_spec hex
  refine ⟨n, hlo, ?_⟩
  by_cases hn : n = 0
  · rw [hn, pow_zero]
    linarith only [hW]
  · have hnpos : 0 < n := by omega
    have hprev := Nat.find_min hex (show n - 1 < n by omega)
    have hprev' : (2 : ℝ) ^ (n - 1) < W := lt_of_not_ge hprev
    have heq : n = (n - 1) + 1 := by omega
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by conv_lhs => rw [heq, pow_succ]
      _ ≤ 2 * W := by linarith only [hprev']

noncomputable def incidencePairCodegree {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) : Sym2 L → ℕ :=
  Sym2.lift ⟨incidenceCodegree N, incidenceCodegree_symm N⟩

@[simp] theorem incidencePairCodegree_mk {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (x z : L) : incidencePairCodegree N s(x, z) = incidenceCodegree N x z := rfl

noncomputable def positiveCodegreeGraph {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (Q : SimpleGraph L) : SimpleGraph L where
  Adj x z := Q.Adj x z ∧ 0 < incidenceCodegree N x z
  symm.symm x z h := ⟨h.1.symm, by simpa only [incidenceCodegree_symm N x z] using h.2⟩
  loopless.irrefl x h := Q.irrefl h.1

theorem positiveCodegreeGraph_adj {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (Q : SimpleGraph L) (x z : L) :
    (positiveCodegreeGraph N Q).Adj x z ↔ Q.Adj x z ∧ 0 < incidenceCodegree N x z := Iff.rfl

noncomputable def reverseCodegreeBand {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (n j : ℕ) : SimpleGraph L :=
  indexedEdgeGraph (positiveCodegreeGraph N (lightIncidenceGraph N W))
    (fun e => n - 1 - Nat.log 2 (incidencePairCodegree N e)) j

theorem reverseCodegreeBand_adj {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (n j : ℕ) (x z : L) :
    (reverseCodegreeBand N W n j).Adj x z ↔
      x ≠ z ∧ (incidenceCodegree N x z : ℝ) < W ∧
        0 < incidenceCodegree N x z ∧ n - 1 - Nat.log 2 (incidenceCodegree N x z) = j := by
  rw [reverseCodegreeBand, indexedEdgeGraph_adj, incidencePairCodegree_mk]
  change ((x ≠ z ∧ (incidenceCodegree N x z : ℝ) < W) ∧ 0 < incidenceCodegree N x z) ∧ _ ↔ _
  tauto

/-- Reverse dyadic bands have thresholds proportional to the original
heavy-pair cutoff. Their index does not introduce a logarithm of P. -/
theorem reverseCodegreeBand_bounds {L R : Type*} [DecidableEq L] [Fintype R]
    (N : R → Finset L) (W : ℝ) (n j : ℕ) (hW : W ≤ (2 : ℝ) ^ n)
    (x z : L) (hadj : (reverseCodegreeBand N W n j).Adj x z) :
    j < n ∧ 2 ^ (n - (j + 1)) ≤ incidenceCodegree N x z ∧
      incidenceCodegree N x z < 2 ^ (n - j) := by
  obtain ⟨_, hupper, hpos, hindex⟩ := (reverseCodegreeBand_adj N W n j x z).mp hadj
  have hlt : incidenceCodegree N x z < 2 ^ n := by exact_mod_cast hupper.trans_le hW
  have hlog : Nat.log 2 (incidenceCodegree N x z) < n := Nat.log_lt_of_lt_pow hpos.ne' hlt
  have hlo := Nat.pow_log_le_self 2 hpos.ne'
  have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (incidenceCodegree N x z)
  have heq₁ : n - (j + 1) = Nat.log 2 (incidenceCodegree N x z) := by omega
  have heq₂ : n - j = Nat.log 2 (incidenceCodegree N x z) + 1 := by omega
  exact ⟨by omega, by simpa only [heq₁] using hlo, by simpa only [heq₂] using hhi⟩

end Erdos911
