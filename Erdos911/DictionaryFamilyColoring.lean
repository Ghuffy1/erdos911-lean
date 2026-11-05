import Erdos911.CheapMonochromaticBlock
import Erdos911.DegreeChargePacking

namespace Erdos911

/-- A single host coloring forces any disjoint monochromatic family
of the prescribed large-right blocks to exceed the host degree budget. -/
theorem exists_dictionary_family_coloring {I V : Type*} [Fintype I]
    [Fintype V] [DecidableEq V] (A R : I → Type*)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    (N : ∀ i, R i → Finset (A i)) (q : ℕ) (hq : 2 ^ 32 ≤ q)
    (hrow : ∀ i y, (N i y).card = q)
    (hA : ∀ i, Fintype.card (A i) ≤ dictionaryLeftSize q)
    (hR : ∀ i, 128 * q ^ 69 ≤ Fintype.card (R i))
    (hpos : 0 < ∑ i, Fintype.card (R i))
    (K : SimpleGraph V) [DecidableRel K.Adj] :
    ∃ χ : Sym2 V → Bool, ∀ g : ∀ i, (incidenceGraph (N i)).Copy K,
      Function.Injective (fun v : (Σ i, A i ⊕ R i) => g v.1 v.2) →
      ∀ b : I → Bool,
      (∀ i y x, x ∈ N i y → χ s(g i (Sum.inl x), g i (Sum.inr y)) = b i) →
        7 * dictionaryDegreeCharge q * (∑ i, Fintype.card (R i)) < 16 * K.edgeFinset.card := by
  classical
  obtain ⟨c, hc⟩ := exists_concrete_dictionary_labels K q
  obtain ⟨f, hf⟩ := exists_dictionary_row_assignment K q hq
  obtain ⟨ω, hω⟩ := exists_target_block_dictionary A R N q (by norm_num at hq; omega) hA
    (fun i => (Fintype.card (R i) : ℝ)) (fun i => Nat.cast_nonneg _)
  refine ⟨dictionaryEdgeColor K q c f ω, ?_⟩
  intro g hg b hb
  let B := (Finset.univ : Finset I).filter (fun i => BlockDictionaryGood (N i) q ω)
  let d := fun i => ∑ v : A i ⊕ R i, K.degree (g i v)
  have hweight : 7 * (∑ i, Fintype.card (R i)) ≤ 8 * (∑ i ∈ B, Fintype.card (R i)) := by
    have heq : (∑ i ∈ B, (Fintype.card (R i) : ℝ)) =
        ∑ i, if BlockDictionaryGood (N i) q ω then (Fintype.card (R i) : ℝ) else 0 := by
      dsimp only [B]
      rw [Finset.sum_filter]
    rw [← heq] at hω
    have hh : 7 * (∑ i, (Fintype.card (R i) : ℝ)) ≤
        8 * (∑ i ∈ B, (Fintype.card (R i) : ℝ)) := by linarith only [hω]
    exact_mod_cast hh
  have hcharge (i : I) (hi : i ∈ B) : dictionaryDegreeCharge q * Fintype.card (R i) < d i := by
    apply Nat.lt_of_not_ge
    exact no_cheap_monochromatic_block (N i) K (g i) q hq (hrow i) (hA i) (hR i)
      c hc f hf ω (Finset.mem_filter.mp hi).2 (b i) (hb i)
  have hbudget : (∑ i, d i) ≤ 2 * K.edgeFinset.card := by
    have hh := injective_degree_sum_le K (fun v : (Σ i, A i ⊕ R i) => g v.1 v.2) hg
    simpa only [Fintype.sum_sigma] using hh
  have hh := retained_degree_charge_bound B (fun i => Fintype.card (R i)) d
    (dictionaryDegreeCharge q) (2 * K.edgeFinset.card) hpos hweight hcharge hbudget
  nlinarith only [hh]

end Erdos911
