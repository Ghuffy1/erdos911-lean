import Erdos911.CopyStarWitnesses

namespace Erdos911

theorem common_filter_card_lower {I E : Type*} [Fintype I] [DecidableEq I] [DecidableEq E]
    (N : Finset E) (p : I → E → Prop) [DecidableRel p] :
    N.card ≤ (N.filter (fun x => ∀ i, p i x)).card +
      ∑ i, (N.filter (fun x => ¬p i x)).card := by
  classical
  let bad := N.filter (fun x => ¬∀ i, p i x)
  have hsub : bad ⊆ Finset.univ.biUnion (fun i => N.filter (fun x => ¬p i x)) := by
    intro x hx
    obtain ⟨hxN, hbad⟩ := Finset.mem_filter.mp hx
    push Not at hbad
    obtain ⟨i, hi⟩ := hbad
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hxN, hi⟩⟩
  have hbadcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsplit := Finset.card_filter_add_card_filter_not (s := N) (fun x => ∀ i, p i x)
  dsimp only [bad] at hbadcard
  omega

theorem common_filter_half_card {I E : Type*} [Fintype I] [DecidableEq I] [DecidableEq E]
    (N : Finset E) (p : I → E → Prop) [DecidableRel p] (ε : ℝ)
    (hbudget : (Fintype.card I : ℝ) * ε ≤ 1 / 2)
    (hlarge : ∀ i, (1 - ε) * N.card ≤ ((N.filter (p i)).card : ℝ)) :
    (N.card : ℝ) ≤ 2 * (N.filter (fun x => ∀ i, p i x)).card := by
  have hbad (i : I) : ((N.filter (fun x => ¬p i x)).card : ℝ) ≤ ε * N.card := by
    have hsum := Finset.card_filter_add_card_filter_not (s := N) (p i)
    have hreal : ((N.filter (p i)).card : ℝ) + (N.filter (fun x => ¬p i x)).card = N.card := by
      exact_mod_cast hsum
    nlinarith only [hreal, hlarge i]
  have hsum : (∑ i, ((N.filter (fun x => ¬p i x)).card : ℝ)) ≤
      (Fintype.card I : ℝ) * ε * N.card := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) => hbad i)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h
  have hbound : (N.card : ℝ) ≤ (N.filter (fun x => ∀ i, p i x)).card +
      ∑ i, ((N.filter (fun x => ¬p i x)).card : ℝ) := by
    exact_mod_cast common_filter_card_lower N p
  have hsmall := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℝ) N.card)
  linarith

noncomputable def tupleGoodNeighbors {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : SimpleGraph W)
    (f : V → W) (v : V) {s : ℕ} (q : Fin s → Option W) : Finset V := by
  classical
  exact (G.neighborFinset v).filter (fun u => ∀ i x, q i = some x → J.Adj x (f u))

noncomputable def slotGoodNeighbors {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : SimpleGraph W)
    (f : V → W) (v : V) (q : Option W) : Finset V := by
  classical
  exact (G.neighborFinset v).filter (fun u => ∀ x, q = some x → J.Adj x (f u))

theorem mem_tupleGoodNeighbors {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : SimpleGraph W)
    (f : V → W) (v u : V) {s : ℕ} (q : Fin s → Option W) :
    u ∈ tupleGoodNeighbors G J f v q ↔ G.Adj v u ∧ ∀ i x, q i = some x → J.Adj x (f u) := by
  classical
  simp only [tupleGoodNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]

theorem mem_slotGoodNeighbors {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : SimpleGraph W)
    (f : V → W) (v u : V) (q : Option W) :
    u ∈ slotGoodNeighbors G J f v q ↔ G.Adj v u ∧ ∀ x, q = some x → J.Adj x (f u) := by
  classical
  simp only [slotGoodNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]

theorem tupleGoodNeighbors_half_card {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (J : SimpleGraph W)
    (f : V → W) (v : V) {s : ℕ} (q : Fin s → Option W) (ε : ℝ)
    (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hlarge : ∀ i, (1 - ε) * G.degree v ≤
      ((slotGoodNeighbors G J f v (q i)).card : ℝ)) :
    (G.degree v : ℝ) ≤ 2 * (tupleGoodNeighbors G J f v q).card := by
  classical
  let p := fun (i : Fin s) (u : V) => ∀ x, q i = some x → J.Adj x (f u)
  let : DecidableRel p := fun i u => Classical.propDecidable (p i u)
  have hslot (i : Fin s) : (G.neighborFinset v).filter (p i) = slotGoodNeighbors G J f v (q i) := by
    ext u
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, mem_slotGoodNeighbors]
    rfl
  have h := common_filter_half_card (G.neighborFinset v) p ε
    (by simpa only [Fintype.card_fin] using hbudget) (by
      intro i
      simpa only [G.card_neighborFinset_eq_degree, hslot i] using hlarge i)
  rw [G.card_neighborFinset_eq_degree] at h
  apply h.trans_eq
  apply congrArg (fun n : ℕ => (2 : ℝ) * n)
  apply congrArg Finset.card
  ext u
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, mem_tupleGoodNeighbors]
  rfl

theorem tupleGoodNeighbors_common_mem {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : V → W) (v u : V)
    {s : ℕ} (q : Fin s → Option W) (hu : u ∈ tupleGoodNeighbors G J f v q) :
    f u ∈ tupleCommonNeighbors J q := by
  classical
  have h := ((mem_tupleGoodNeighbors G J f v u q).mp hu).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

theorem tupleGoodNeighbors_edges_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel J.Adj] (f : G.Copy H) (v : V)
    {s : ℕ} (q : Fin s → Option W) (hactive : ¬inactiveStarTuple q) :
    (tupleGoodNeighbors G J f v q).card ≤
      (copyRawEdges f ∩ starWitnessEdges J (f v) q).card := by
  classical
  have hf : Function.Injective (f : V → W) := f.injective
  have hinj : Function.Injective (fun u : V => s(f v, f u)) := by
    intro u w h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hf h.2
    · exact hf (h.2.trans h.1)
  have hsub : (tupleGoodNeighbors G J f v q).image (fun u => s(f v, f u)) ⊆
      copyRawEdges f ∩ starWitnessEdges J (f v) q := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    have huv : G.Adj v u := ((mem_tupleGoodNeighbors G J f v u q).mp hu).1
    refine Finset.mem_inter.mpr ⟨?_, ?_⟩
    · exact (mem_copyRawEdges_iff_exists f _).mpr ⟨⟨s(v, u), huv⟩, rfl⟩
    · unfold starWitnessEdges
      rw [ite_eq_right hactive]
      exact Finset.mem_image.mpr ⟨f u, tupleGoodNeighbors_common_mem G J f v u q hu, rfl⟩
  calc
    (tupleGoodNeighbors G J f v q).card =
        ((tupleGoodNeighbors G J f v q).image (fun u => s(f v, f u))).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

end Erdos911
