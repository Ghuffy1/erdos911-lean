import Erdos911.DictionaryFamilyColoring
import Erdos911.IncidenceCenterBlocks
import Erdos911.LargeRightBlockReduction

namespace Erdos911

/-- The dictionary obstruction applies to every host graph, including
hosts with no maximum-degree bound. -/
theorem large_right_block_size_ramsey {L R : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    (N : R → Finset L) (U : Finset R) (f : R → L) (X : L → Finset L)
    (q : ℕ) (hq : 2 ^ 32 ≤ q)
    (he : 0 < (incidenceGraph N).edgeSet.ncard)
    (hrow : ∀ y ∈ U, (N y).card = q ∧ N y ⊆ X (f y))
    (hzero : ∀ y ∉ U, N y = ∅)
    (hfiber : ∀ y ∈ U, 128 * q ^ 69 ≤ (U.filter (fun z => f z = f y)).card)
    (hdisjoint : ∀ y ∈ U, ∀ z ∈ U, f y ≠ f z → Disjoint (X (f y)) (X (f z)))
    (hX : ∀ x, (X x).card ≤ q ^ 20) :
    (7 / 16 : ℝ) * (q : ℝ) ^ 49 * (incidenceGraph N).edgeSet.ncard <
      (SimpleGraph.sizeRamsey (incidenceGraph N) (incidenceGraph N) : ℝ) := by
  classical
  let I := ↥(U.image f)
  let A := fun i : I => ↥(X i.val)
  let B := fun i : I => ↥(centerRows U f i.val)
  let S := fun i : I => centerNeighborhood (U := U) (f := f) N X i.val
  have hSrow (i : I) (y : B i) : (S i y).card = q := by
    rw [centerNeighborhood_card N U f X (fun y hy => (hrow y hy).2)]
    exact (hrow y.val (Finset.mem_filter.mp y.property).1).1
  have hSA (i : I) : Fintype.card (A i) ≤ dictionaryLeftSize q := by
    simpa only [A, Fintype.card_coe, dictionaryLeftSize] using hX i.val
  have hSB (i : I) : 128 * q ^ 69 ≤ Fintype.card (B i) := by
    obtain ⟨y, hy, hfi⟩ := Finset.mem_image.mp i.property
    have h := hfiber y hy
    change 128 * q ^ 69 ≤ Fintype.card ↥(centerRows U f i.val)
    rw [Fintype.card_coe]
    simpa only [centerRows, hfi] using h
  have hsum : (∑ i : I, Fintype.card (B i)) = U.card := centerRows_sum U f
  have hedge : (incidenceGraph N).edgeSet.ncard = q * U.card := by
    rw [← Set.fintypeCard_eq_ncard, ← (incidenceGraph N).edgeFinset_card, incidenceGraph_edge_count]
    have hterms (y : R) : (N y).card = if y ∈ U then q else 0 := by
      by_cases hy : y ∈ U
      · simp only [hy, ite_true, (hrow y hy).1]
      · simp only [hy, ite_false, hzero y hy, Finset.card_empty]
    simp_rw [hterms]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hUpos : 0 < U.card := by rw [hedge] at he; exact Nat.pos_of_mul_pos_left he
  have hsumpos : 0 < ∑ i : I, Fintype.card (B i) := by rwa [hsum]
  have hdisj : ∀ x ∈ U.image f, ∀ z ∈ U.image f, x ≠ z → Disjoint (X x) (X z) := by
    intro x hx z hz hxz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hdisjoint y hy w hw hxz
  apply (sizeRamsey_real_gt_iff _ _ _).mpr
  intro k K hbudget
  obtain ⟨χ, hχ⟩ := exists_dictionary_family_coloring A B S q hq hSrow hSA hSB hsumpos K
  have hbudgetN : 16 * K.edgeFinset.card ≤
      7 * dictionaryDegreeCharge q * (∑ i : I, Fintype.card (B i)) := by
    rw [hsum, dictionaryDegreeCharge]
    have hK : K.edgeSet.ncard = K.edgeFinset.card := by
      rw [K.edgeFinset_card, Set.fintypeCard_eq_ncard]
    rw [hedge, hK] at hbudget
    push_cast at hbudget
    have hp : (q : ℝ) ^ 49 * q = (q : ℝ) ^ 50 := by ring
    have hh : (16 : ℝ) * K.edgeFinset.card ≤ 7 * (q : ℝ) ^ 50 * U.card := by
      nlinarith only [hbudget, hp]
    exact_mod_cast hh
  have hfree (b : Bool) : ¬ (incidenceGraph N).IsContained (edgeColorClass K (fun e => χ e.val) b) := by
    rintro ⟨p⟩
    let pg : (incidenceGraph N).Copy K :=
      (SimpleGraph.Copy.ofLE _ _ (edgeColorClass_le K (fun e => χ e.val) b)).comp p
    let g : ∀ i : I, (incidenceGraph (S i)).Copy K := fun i =>
      pg.comp (centerBlockCopy N U f X i.val)
    have hginj : Function.Injective (fun v : (Σ i : I, A i ⊕ B i) => g v.1 v.2) :=
      pg.injective.comp (centerVertexMap_sigma_injective U f X hdisj)
    have hmono (i : I) (y : B i) (x : A i) (hxy : x ∈ S i y) :
        χ s(g i (Sum.inl x), g i (Sum.inr y)) = b := by
      have hadj : (incidenceGraph (S i)).Adj (Sum.inl x) (Sum.inr y) := hxy
      have hm := (p.comp (centerBlockCopy N U f X i.val)).toHom.map_adj hadj
      exact hm.choose_spec
    have hlt := hχ g hginj (fun _ => b) hmono
    exact (not_lt_of_ge hbudgetN) hlt
  refine ⟨edgeColorClass K (fun e => χ e.val) false,
    edgeColorClass_le K (fun e => χ e.val) false, hfree false, ?_⟩
  rw [edgeColorClass_complement]
  exact hfree true

theorem large_right_block_ramsey_statement : LargeRightBlockRamseyStatement := by
  refine ⟨2 ^ 32, ?_⟩
  intro q hq L R _ _ _ _ N U f X he hrow hzero hfiber hdisjoint hX
  exact large_right_block_size_ramsey N U f X q hq he hrow hzero hfiber hdisjoint hX

end Erdos911
