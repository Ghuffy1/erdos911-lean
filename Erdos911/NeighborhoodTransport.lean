import Erdos911.NeighborhoodNormalization

namespace Erdos911

def relabelNeighborhoods {L R L' R' : Type*} (N : R → Finset L)
    (eL : L' ≃ L) (eR : R' ≃ R) : R' → Finset L' :=
  fun y => (N (eR y)).map eL.symm.toEmbedding

theorem mem_relabelNeighborhoods {L R L' R' : Type*} (N : R → Finset L)
    (eL : L' ≃ L) (eR : R' ≃ R) (x : L') (y : R') :
    x ∈ relabelNeighborhoods N eL eR y ↔ eL x ∈ N (eR y) := by
  classical
  simp only [relabelNeighborhoods, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have h : z = eL x := by rw [← hzx, eL.apply_symm_apply]
    exact h ▸ hz
  · intro hx
    exact ⟨eL x, hx, eL.symm_apply_apply x⟩

theorem relabelNeighborhoods_row_card {L R L' R' : Type*} (N : R → Finset L)
    (eL : L' ≃ L) (eR : R' ≃ R) (y : R') :
    (relabelNeighborhoods N eL eR y).card = (N (eR y)).card :=
  Finset.card_map _

theorem relabelNeighborhoods_column_card {L R L' R' : Type*}
    [Fintype R] [Fintype R'] [DecidableEq L] [DecidableEq L']
    (N : R → Finset L) (eL : L' ≃ L) (eR : R' ≃ R) (x : L') :
    ((Finset.univ : Finset R').filter (fun y => x ∈ relabelNeighborhoods N eL eR y)).card =
      ((Finset.univ : Finset R).filter (fun y => eL x ∈ N y)).card := by
  classical
  apply Finset.card_bij (fun y _ => eR y)
  · intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_relabelNeighborhoods N eL eR x y).mp (Finset.mem_filter.mp hy).2⟩
  · intro u _ v _ h
    exact eR.injective h
  · intro y hy
    refine ⟨eR.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    apply (mem_relabelNeighborhoods N eL eR x (eR.symm y)).mpr
    simpa only [eR.apply_symm_apply] using (Finset.mem_filter.mp hy).2

/-- The exact-neighborhood normalization is independent of the chosen
finite labels on either side of a bipartite graph. -/
theorem exists_degree_normalization_general {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (N : R → Finset L) (q a b r : ℕ) (hq : ∀ y, q ≤ (N y).card)
    (ha : ∀ x, (Finset.univ.filter (fun y => x ∈ N y)).card ≤ a)
    (hb : ∀ y, (N y).card ≤ b)
    (hr : ∀ x, r ≤ (Finset.univ.filter (fun y => x ∈ N y)).card)
    (hc : Real.exp 1 * Real.exp (-((q : ℝ) / b * r) / 8) * ((a * b : ℕ) + 1) ≤ 1) :
    ∃ S : R → Finset L, (∀ y, S y ⊆ N y ∧ (S y).card = q) ∧
      ∀ x, (q : ℝ) / b * r / 2 < ((Finset.univ.filter (fun y => x ∈ S y)).card : ℝ) := by
  classical
  let eL := (Fintype.equivFin L).symm
  let eR := (Fintype.equivFin R).symm
  let N' := relabelNeighborhoods N eL eR
  have hq' : ∀ y, q ≤ (N' y).card := by
    intro y
    rw [relabelNeighborhoods_row_card]
    exact hq _
  have ha' : ∀ x, (Finset.univ.filter (fun y => x ∈ N' y)).card ≤ a := by
    intro x
    rw [relabelNeighborhoods_column_card]
    exact ha _
  have hb' : ∀ y, (N' y).card ≤ b := by
    intro y
    rw [relabelNeighborhoods_row_card]
    exact hb _
  have hr' : ∀ x, r ≤ (Finset.univ.filter (fun y => x ∈ N' y)).card := by
    intro x
    rw [relabelNeighborhoods_column_card]
    exact hr _
  obtain ⟨S', hS', hleft⟩ := exists_degree_normalization N' q a b r hq' ha' hb' hr' hc
  let S := relabelNeighborhoods S' eL.symm eR.symm
  refine ⟨S, ?_, ?_⟩
  · intro y
    constructor
    · intro x hx
      have hx' := (mem_relabelNeighborhoods S' eL.symm eR.symm x y).mp hx
      have hN := (hS' (eR.symm y)).1 hx'
      have hN' := (mem_relabelNeighborhoods N eL eR (eL.symm x) (eR.symm y)).mp hN
      simpa only [eL.apply_symm_apply, eR.apply_symm_apply] using hN'
    · rw [relabelNeighborhoods_row_card]
      exact (hS' _).2
  · intro x
    rw [relabelNeighborhoods_column_card]
    exact hleft _

end Erdos911
