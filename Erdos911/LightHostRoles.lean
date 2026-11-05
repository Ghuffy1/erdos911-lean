import Erdos911.HighImageDegreeMass
import Erdos911.PairHostColoring

namespace Erdos911

noncomputable def lightHostLeftRole {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (P : ℝ) (D : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => P ≤ (K.degree v : ℝ) ∧ K.degree v ≤ D)

noncomputable def lightHostRightRole {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => 0 < K.degree v ∧ K.degree v ≤ D)

theorem mem_lightHostLeftRole {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (P : ℝ) (D : ℕ) (v : V) :
    v ∈ lightHostLeftRole K P D ↔ P ≤ (K.degree v : ℝ) ∧ K.degree v ≤ D := by
  classical
  simp [lightHostLeftRole]

theorem mem_lightHostRightRole {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) (v : V) :
    v ∈ lightHostRightRole K D ↔ 0 < K.degree v ∧ K.degree v ≤ D := by
  classical
  simp [lightHostRightRole]

theorem lightHostRoles_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (P : ℝ) (DL DR : ℕ)
    (hDR : (DR : ℝ) < P) :
    Disjoint (lightHostLeftRole K P DL) (lightHostRightRole K DR) := by
  apply Finset.disjoint_left.mpr
  intro v hL hR
  have hl := ((mem_lightHostLeftRole K P DL v).mp hL).1
  have hr := ((mem_lightHostRightRole K DR v).mp hR).2
  have hr' : (K.degree v : ℝ) ≤ DR := by exact_mod_cast hr
  linarith only [hl, hr', hDR]

/-- Isolated host vertices do not increase the number of available rows. -/
theorem lightHostRightRole_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (D : ℕ) :
    (lightHostRightRole K D).card ≤ 2 * K.edgeSet.ncard := by
  classical
  have hs : lightHostRightRole K D ⊆ Finset.univ.filter (fun v => 1 ≤ K.degree v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((mem_lightHostRightRole K D v).mp hv).1⟩
  have h := (Finset.card_le_card hs).trans (by simpa only [one_mul] using high_degree_card_bound K 1)
  simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using h

end Erdos911
