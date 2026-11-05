import Erdos911.HeavyIncidenceGeometry
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Erdos911

noncomputable def graphWalkBall {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ → V → Finset V
  | 0, v => {v}
  | n + 1, v => (closedNeighborFinset G v).biUnion (graphWalkBall G n)

theorem mem_graphWalkBall_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (u v : V) :
    v ∈ graphWalkBall G n u ↔ ∃ p : G.Walk u v, p.length ≤ n := by
  induction n generalizing u v with
  | zero =>
    simp only [graphWalkBall, Finset.mem_singleton]
    constructor
    · intro h
      subst v
      exact ⟨.nil, by simp⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => rfl
      | cons hadj p => simp at hp
  | succ n ih =>
    rw [graphWalkBall, Finset.mem_biUnion]
    constructor
    · rintro ⟨z, huz, hzv⟩
      obtain ⟨p, hp⟩ := (ih z v).mp hzv
      rcases Finset.mem_insert.mp huz with hzu | huz
      · subst z
        exact ⟨p, hp.trans (Nat.le_succ n)⟩
      · exact ⟨.cons ((G.mem_neighborFinset u z).mp huz) p, by simpa using Nat.succ_le_succ hp⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil =>
        refine ⟨u, Finset.mem_insert_self _ _, ?_⟩
        exact (ih u u).mpr ⟨.nil, by simp⟩
      | cons hadj p =>
        refine ⟨_, Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr hadj), ?_⟩
        apply (ih _ _).mpr
        exact ⟨p, by simpa using hp⟩

theorem graphWalkBall_symm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (u v : V) :
    v ∈ graphWalkBall G n u ↔ u ∈ graphWalkBall G n v := by
  simp only [mem_graphWalkBall_iff]
  constructor <;> rintro ⟨p, hp⟩ <;> exact ⟨p.reverse, by simpa using hp⟩

/-- Ball size depends only on the degree bound and the radius, with
staying in place accounting for the added one. -/
theorem graphWalkBall_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, G.degree v ≤ D)
    (n : ℕ) (v : V) : (graphWalkBall G n v).card ≤ (D + 1) ^ n := by
  induction n generalizing v with
  | zero => simp only [graphWalkBall, Finset.card_singleton, pow_zero, le_refl]
  | succ n ih =>
    calc
      (graphWalkBall G (n + 1) v).card ≤ ∑ w ∈ closedNeighborFinset G v, (graphWalkBall G n w).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ closedNeighborFinset G v, (D + 1) ^ n := Finset.sum_le_sum (fun w _ => ih w)
      _ = (G.degree v + 1) * (D + 1) ^ n := by simp [closedNeighborFinset_card]
      _ ≤ (D + 1) * (D + 1) ^ n := Nat.mul_le_mul_right _ (Nat.add_le_add_right (hD v) 1)
      _ = (D + 1) ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

noncomputable def boundedWalkGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ v ∈ graphWalkBall G n u
  symm.symm u v h := ⟨h.1.symm, (graphWalkBall_symm G n u v).mp h.2⟩
  loopless.irrefl _ h := h.1 rfl

theorem boundedWalkGraph_degree_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, G.degree v ≤ D)
    (n : ℕ) (v : V) :
    letI : DecidableRel (boundedWalkGraph G n).Adj := Classical.decRel _
    (boundedWalkGraph G n).degree v ≤ (D + 1) ^ n := by
  classical
  have hsub : (boundedWalkGraph G n).neighborFinset v ⊆ graphWalkBall G n v := by
    intro w hw
    exact ((boundedWalkGraph G n).mem_neighborFinset v w).mp hw |>.2
  have h := (Finset.card_le_card hsub).trans (graphWalkBall_card_le G D hD n v)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using h

end Erdos911
