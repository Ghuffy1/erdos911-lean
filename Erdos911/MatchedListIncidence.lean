import Erdos911.CopyImages

namespace Erdos911

/-- Injective representatives in clique lists control how many lists can
contain the same candidate. -/
theorem list_incidence_le_at {I W : Type*}
    [Fintype I] [Fintype W] [DecidableEq W]
    (Q : SimpleGraph W) [DecidableRel Q.Adj] (L : I → Finset W)
    (f : I → W) (hf : Function.Injective f) (hmem : ∀ i, f i ∈ L i)
    (hclique : ∀ i, ∀ x ∈ L i, ∀ y ∈ L i, x ≠ y → Q.Adj x y)
    (q : ℕ) (y : W) (hdegree : Q.degree y < q) :
    (Finset.univ.filter (fun i => y ∈ L i)).card ≤ q := by
  classical
  let S := Finset.univ.filter (fun i => y ∈ L i)
  have hsub : S.image f ⊆ insert y (Q.neighborFinset y) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    by_cases hfy : f i = y
    · exact Finset.mem_insert.mpr (Or.inl hfy)
    · apply Finset.mem_insert.mpr
      right
      apply (Q.mem_neighborFinset y (f i)).mpr
      exact hclique i y (Finset.mem_filter.mp hi).2 (f i) (hmem i) (fun h => hfy h.symm)
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injective S hf).symm
    _ ≤ (insert y (Q.neighborFinset y)).card := Finset.card_le_card hsub
    _ ≤ (Q.neighborFinset y).card + 1 := Finset.card_insert_le _ _
    _ = Q.degree y + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ q := by omega

theorem list_incidence_le_of_injective_representatives {I W : Type*}
    [Fintype I] [Fintype W] [DecidableEq W]
    (Q : SimpleGraph W) [DecidableRel Q.Adj] (L : I → Finset W)
    (f : I → W) (hf : Function.Injective f) (hmem : ∀ i, f i ∈ L i)
    (hclique : ∀ i, ∀ x ∈ L i, ∀ y ∈ L i, x ≠ y → Q.Adj x y)
    (q : ℕ) (hdegree : ∀ y, Q.degree y < q) (y : W) :
    (Finset.univ.filter (fun i => y ∈ L i)).card ≤ q :=
  list_incidence_le_at Q L f hf hmem hclique q y (hdegree y)

/-- A mark meeting at most `q` candidates influences at most `q^2`
matched clique-list indicators. -/
theorem matched_lists_read_bound_on {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]
    (Q : SimpleGraph W) [DecidableRel Q.Adj] (L : I → Finset W)
    (f : I → W) (hf : Function.Injective f) (hmem : ∀ i, f i ∈ L i)
    (hclique : ∀ i, ∀ x ∈ L i, ∀ y ∈ L i, x ≠ y → Q.Adj x y)
    (q : ℕ) (B : Finset W) (hB : B.card ≤ q) (hdegree : ∀ y ∈ B, Q.degree y < q) :
    (Finset.univ.filter (fun i => ¬Disjoint B (L i))).card ≤ q * q := by
  classical
  let through (y : W) := Finset.univ.filter (fun i => y ∈ L i)
  have hsub : Finset.univ.filter (fun i => ¬Disjoint B (L i)) ⊆ B.biUnion through := by
    intro i hi
    obtain ⟨y, hyB, hyL⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
    exact Finset.mem_biUnion.mpr ⟨y, hyB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyL⟩⟩
  calc
    _ ≤ (B.biUnion through).card := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ B, (through y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ B, q := Finset.sum_le_sum (fun y hy =>
      list_incidence_le_at Q L f hf hmem hclique q y (hdegree y hy))
    _ = B.card * q := by simp
    _ ≤ q * q := Nat.mul_le_mul_right q hB

theorem matched_lists_read_bound {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]
    (Q : SimpleGraph W) [DecidableRel Q.Adj] (L : I → Finset W)
    (f : I → W) (hf : Function.Injective f) (hmem : ∀ i, f i ∈ L i)
    (hclique : ∀ i, ∀ x ∈ L i, ∀ y ∈ L i, x ≠ y → Q.Adj x y)
    (q : ℕ) (hdegree : ∀ y, Q.degree y < q)
    (B : Finset W) (hB : B.card ≤ q) :
    (Finset.univ.filter (fun i => ¬Disjoint B (L i))).card ≤ q * q :=
  matched_lists_read_bound_on Q L f hf hmem hclique q B hB (fun y _ => hdegree y)

end Erdos911
