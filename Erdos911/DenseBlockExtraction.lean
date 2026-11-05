import Erdos911.RectangleEdges
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.Powerset

namespace Erdos911

structure RectangleBlock (V : Type*) where
  left : Finset V
  right : Finset V
  edges : Finset (Sym2 V)
  deriving DecidableEq

noncomputable instance rectangleBlockFintype {V : Type*} [Fintype V] :
    Fintype (RectangleBlock V) := by
  classical
  apply Fintype.ofInjective (fun B : RectangleBlock V => (B.left, B.right, B.edges))
  intro B C h
  cases B
  cases C
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

def RectangleBlock.Valid {V : Type*} (G : SimpleGraph V) (q : ℕ) (ρ : ℝ)
    (B : RectangleBlock V) : Prop :=
  B.left.card = q ∧ B.right.card = q ∧ Disjoint B.left B.right ∧
    B.edges ⊆ rectangleEdges G B.left B.right ∧ ρ * q * q < (B.edges.card : ℝ)

def ValidBlockPacking {V : Type*} (G : SimpleGraph V) (q : ℕ) (ρ : ℝ)
    (P : Finset (RectangleBlock V)) : Prop :=
  (∀ B ∈ P, B.Valid G q ρ) ∧ (P : Set (RectangleBlock V)).PairwiseDisjoint RectangleBlock.edges

theorem RectangleBlock.Valid.mono {V : Type*} {G H : SimpleGraph V}
    {q : ℕ} {ρ : ℝ} {B : RectangleBlock V} (hB : B.Valid G q ρ) (hGH : G ≤ H) :
    B.Valid H q ρ :=
  ⟨hB.1, hB.2.1, hB.2.2.1,
    hB.2.2.2.1.trans (rectangleEdges_mono hGH B.left B.right), hB.2.2.2.2⟩

theorem ValidBlockPacking.mono {V : Type*} {G H : SimpleGraph V}
    {q : ℕ} {ρ : ℝ} {P : Finset (RectangleBlock V)}
    (hP : ValidBlockPacking G q ρ P) (hGH : G ≤ H) : ValidBlockPacking H q ρ P :=
  ⟨fun B hB => (hP.1 B hB).mono hGH, hP.2⟩

noncomputable def blockEdgeUnion {V : Type*} (P : Finset (RectangleBlock V)) :
    Finset (Sym2 V) := by
  classical
  exact P.biUnion RectangleBlock.edges

theorem mem_blockEdgeUnion {V : Type*} (P : Finset (RectangleBlock V)) (e : Sym2 V) :
    e ∈ blockEdgeUnion P ↔ ∃ B ∈ P, e ∈ B.edges := by
  classical
  simp only [blockEdgeUnion, Finset.mem_biUnion]

theorem RectangleBlock.Valid.support_card {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {q : ℕ} {ρ : ℝ} {B : RectangleBlock V} (hB : B.Valid G q ρ) :
    (B.left ∪ B.right).card = 2 * q := by
  rw [Finset.card_union_of_disjoint hB.2.2.1, hB.1, hB.2.1]
  omega

theorem RectangleBlock.Valid.edges_card_le {V : Type*}
    {G : SimpleGraph V} {q : ℕ} {ρ : ℝ} {B : RectangleBlock V} (hB : B.Valid G q ρ) :
    B.edges.card ≤ q * q := by
  have h := (Finset.card_le_card hB.2.2.2.1).trans (rectangleEdges_card_le G B.left B.right)
  simpa only [hB.1, hB.2.1] using h

theorem validBlockPacking_edgeUnion_subset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (ρ : ℝ)
    (P : Finset (RectangleBlock V)) (hP : ValidBlockPacking G q ρ P) :
    blockEdgeUnion P ⊆ G.edgeFinset := by
  classical
  intro e he
  obtain ⟨B, hB, heB⟩ := (mem_blockEdgeUnion P e).mp he
  exact rectangleEdges_subset_edgeFinset G B.left B.right ((hP.1 B hB).2.2.2.1 heB)

theorem validBlockPacking_count_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (ρ : ℝ)
    (P : Finset (RectangleBlock V)) (hP : ValidBlockPacking G q ρ P) :
    (ρ * q * q) * P.card ≤ G.edgeFinset.card := by
  classical
  calc
    (ρ * q * q) * P.card = ∑ _B ∈ P, ρ * q * q := by simp [mul_comm]
    _ ≤ ∑ B ∈ P, (B.edges.card : ℝ) :=
      Finset.sum_le_sum (fun B hB => (hP.1 B hB).2.2.2.2.le)
    _ = (blockEdgeUnion P).card := by
      rw [blockEdgeUnion, Finset.card_biUnion hP.2, Nat.cast_sum]
    _ ≤ G.edgeFinset.card := by
      exact_mod_cast Finset.card_le_card (validBlockPacking_edgeUnion_subset G q ρ P hP)

/-- A maximal family of edge-disjoint dense blocks leaves no dense
disjoint rectangle. Block supports may overlap. -/
theorem exists_dense_block_packing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ P : Finset (RectangleBlock V), ValidBlockPacking G q ρ P ∧
      ∀ A B : Finset V, A.card = q → B.card = q → Disjoint A B →
        (crossEdges (G.deleteEdges (blockEdgeUnion P : Set (Sym2 V))) A B : ℝ) ≤ ρ * q * q := by
  classical
  let families := Finset.univ.filter (ValidBlockPacking G q ρ)
  have hempty : (∅ : Finset (RectangleBlock V)) ∈ families := by
    simp [families, ValidBlockPacking]
  obtain ⟨P, hPmem, hmax⟩ := Finset.exists_max_image families Finset.card ⟨∅, hempty⟩
  have hP : ValidBlockPacking G q ρ P := (Finset.mem_filter.mp hPmem).2
  refine ⟨P, hP, ?_⟩
  intro A B hA hB hAB
  let J := G.deleteEdges (blockEdgeUnion P : Set (Sym2 V))
  by_contra hsmall
  have hdense : ρ * q * q < ((rectangleEdges J A B).card : ℝ) := by
    rw [rectangleEdges_card J A B hAB]
    exact lt_of_not_ge hsmall
  let C : RectangleBlock V := ⟨A, B, rectangleEdges J A B⟩
  have hC : C.Valid G q ρ :=
    ⟨hA, hB, hAB, rectangleEdges_mono (G.deleteEdges_le _) A B, hdense⟩
  have hCnonempty : C.edges.Nonempty := by
    apply Finset.card_pos.mp
    have hzero : (0 : ℝ) ≤ ρ * q * q := by positivity
    exact_mod_cast hzero.trans_lt hdense
  have hdis : Disjoint C.edges (blockEdgeUnion P) := by
    apply Finset.disjoint_left.mpr
    intro e heC heP
    have heJ := rectangleEdges_subset_edgeFinset J A B heC
    have heout : e ∉ blockEdgeUnion P := by
      have hdiff : e ∈ G.edgeFinset \ blockEdgeUnion P := by
        simpa only [J, SimpleGraph.edgeFinset_deleteEdges] using heJ
      exact (Finset.mem_sdiff.mp hdiff).2
    exact heout heP
  have hCdis : ∀ B ∈ P, Disjoint C.edges B.edges := by
    intro B hB
    apply Finset.disjoint_left.mpr
    intro e heC heB
    exact (Finset.disjoint_left.mp hdis) heC ((mem_blockEdgeUnion P e).mpr ⟨B, hB, heB⟩)
  have hCnot : C ∉ P := by
    intro hCP
    obtain ⟨e, he⟩ := hCnonempty
    exact (Finset.disjoint_left.mp (hCdis C hCP)) he he
  have hinsert : ValidBlockPacking G q ρ (insert C P) := by
    constructor
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hC
      · exact hP.1 B hB
    · intro B hB D hD hBD
      rcases Finset.mem_insert.mp hB with rfl | hB
      · rcases Finset.mem_insert.mp hD with rfl | hD
        · exact (hBD rfl).elim
        · exact hCdis D hD
      · rcases Finset.mem_insert.mp hD with rfl | hD
        · exact (hCdis B hB).symm
        · exact hP.2 hB hD hBD
  have hcard := hmax (insert C P) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinsert⟩)
  rw [Finset.card_insert_of_notMem hCnot] at hcard
  omega

theorem validBlockPacking_capacity_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) (ρ : ℝ)
    (P : Finset (RectangleBlock V)) (hP : ValidBlockPacking G q ρ P)
    (hthreshold : 0 < ρ * q * q) (capacity : RectangleBlock V → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hcapacity : ∀ B ∈ P, capacity B ≤ K) :
    ∑ B ∈ P, capacity B ≤ K * G.edgeFinset.card / (ρ * q * q) := by
  have hcount : (P.card : ℝ) ≤ G.edgeFinset.card / (ρ * q * q) := by
    apply (le_div_iff₀ hthreshold).mpr
    simpa only [mul_comm] using validBlockPacking_count_bound G q ρ P hP
  calc
    (∑ B ∈ P, capacity B) ≤ ∑ _B ∈ P, K := Finset.sum_le_sum hcapacity
    _ = K * P.card := by simp [mul_comm]
    _ ≤ K * (G.edgeFinset.card / (ρ * q * q)) := mul_le_mul_of_nonneg_left hcount hK
    _ = K * G.edgeFinset.card / (ρ * q * q) := by rw [mul_div_assoc]

end Erdos911
