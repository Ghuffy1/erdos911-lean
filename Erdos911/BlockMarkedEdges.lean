import Erdos911.BlockCopyAvoidance

namespace Erdos911

noncomputable def markedBlockEdges {W : Type*} (P : Finset (RectangleBlock W))
    (ω : P → Bool) : Finset (Sym2 W) := by
  classical
  exact (Finset.univ.filter (fun B : P => ω B = true)).biUnion (fun B => B.val.edges)

theorem mem_markedBlockEdges {W : Type*} (P : Finset (RectangleBlock W))
    (ω : P → Bool) (e : Sym2 W) :
    e ∈ markedBlockEdges P ω ↔ ∃ B : P, ω B = true ∧ e ∈ B.val.edges := by
  classical
  simp only [markedBlockEdges, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem copyRawEdges_block_inter_card {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H) (B : RectangleBlock W) :
    (copyRawEdges f ∩ B.edges).card = (copyHostEdges f ∩ blockHostEdges H B).card := by
  classical
  have heq : (copyHostEdges f ∩ blockHostEdges H B).map ⟨Subtype.val, Subtype.val_injective⟩ =
      copyRawEdges f ∩ B.edges := by
    ext e
    constructor
    · intro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_map.mpr ⟨a, (Finset.mem_inter.mp ha).1, rfl⟩,
          (mem_blockHostEdges H B a).mp (Finset.mem_inter.mp ha).2⟩
    · intro he
      obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp (Finset.mem_inter.mp he).1
      apply Finset.mem_map.mpr
      refine ⟨a, Finset.mem_inter.mpr ⟨ha, ?_⟩, hea⟩
      apply (mem_blockHostEdges H B a).mpr
      change a.val = e at hea
      rw [hea]
      exact (Finset.mem_inter.mp he).2
  rw [← heq, Finset.card_map]

/-- Summed block capacities bound the edges of every target copy colored
by a family of marked blocks, even when block supports overlap. -/
theorem markedBlockEdges_copy_capacity {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G.Copy H)
    (P : Finset (RectangleBlock W)) (ω : P → Bool) (c : P → ℝ)
    (hc : ∀ B, ((copyRawEdges f ∩ B.val.edges).card : ℝ) ≤ c B) :
    ((copyRawEdges f ∩ markedBlockEdges P ω).card : ℝ) ≤
      ∑ B, if ω B = true then c B else 0 := by
  classical
  let marked := Finset.univ.filter (fun B : P => ω B = true)
  have heq : copyRawEdges f ∩ markedBlockEdges P ω =
      marked.biUnion (fun B => copyRawEdges f ∩ B.val.edges) := by
    ext e
    simp only [Finset.mem_inter, mem_markedBlockEdges, Finset.mem_biUnion,
      marked, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  calc
    _ = ((marked.biUnion (fun B => copyRawEdges f ∩ B.val.edges)).card : ℝ) := by rw [heq]
    _ ≤ ∑ B ∈ marked, ((copyRawEdges f ∩ B.val.edges).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := marked)
        (t := fun B => copyRawEdges f ∩ B.val.edges)
    _ ≤ ∑ B ∈ marked, c B := Finset.sum_le_sum (fun B _ => hc B)
    _ = ∑ B, if ω B = true then c B else 0 := by simp only [marked, Finset.sum_filter]

theorem marked_block_residual_sparse {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W)
    (P : Finset (RectangleBlock W)) (b : ℕ) (ω : P → Bool)
    (hhits : ∀ f : F.Copy H, b ≤ (touchedBlocks P (copyRawEdges f)).card →
      ∃ B ∈ touchedBlocks P (copyRawEdges f), ω B = true)
    (f : F.Copy (H.deleteEdges (markedBlockEdges P ω : Set (Sym2 W)))) :
    (touchedBlocks P (copyRawEdges
      ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))).card < b := by
  classical
  by_contra hn
  let fH : F.Copy H := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
  obtain ⟨B, hB, hmarked⟩ := hhits fH (Nat.le_of_not_gt hn)
  obtain ⟨e, heB, hef⟩ := Finset.not_disjoint_iff.mp
    ((mem_touchedBlocks P (copyRawEdges fH) B).mp hB)
  have heRaw : e ∈ copyRawEdges f := by simpa only [fH, copyRawEdges_ofLE_comp] using hef
  have heResidual := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e).mp heRaw)
  rw [H.edgeSet_deleteEdges] at heResidual
  exact heResidual.2 ((mem_markedBlockEdges P ω e).mpr ⟨B, hmarked, heB⟩)

/-- A block-marking outcome gives a concrete edge deletion with its blue
capacity bound and the remaining upper bound on block use in red copies. -/
theorem exists_block_pruned_graph {V U W : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U)
    (H : SimpleGraph W) [DecidableRel H.Adj] (hF : F.Connected)
    (P : Finset (RectangleBlock W)) (M : ℕ) (hP : BoundedEdgeBlocks P M)
    (b D : ℕ) (hD : ∀ w, H.degree w ≤ D)
    (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hq : 4 * q ≤ p)
    (hhalf : Real.exp (-p * b / 2) ≤ 1 / 2)
    (hincidence : (M * (Fintype.card V * D ^ (2 * (Fintype.card V - 1))) : ℝ) *
      Real.exp (-p * b / 2) ≤ q)
    (hfactor : Real.exp (2 * q) ≤ 2) (c : P → ℝ) (hc : ∀ B, 0 ≤ c B)
    (hcapacity : ∀ g : G.Copy H, ∀ B, ((copyRawEdges g ∩ B.val.edges).card : ℝ) ≤ c B) :
    ∃ marked : Finset (Sym2 W),
      (∀ g : G.Copy H, ((copyRawEdges g ∩ marked).card : ℝ) ≤ (2 * p) * ∑ B, c B) ∧
      ∀ f : F.Copy (H.deleteEdges (marked : Set (Sym2 W))),
        (touchedBlocks P (copyRawEdges
          ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))).card < b := by
  obtain ⟨ω, hcost, hhits⟩ := exists_block_marks_with_budget F H hF P M hP b D hD
    p q hp₀ hp₁ hq hhalf hincidence hfactor c hc
  refine ⟨markedBlockEdges P ω, ?_, marked_block_residual_sparse F H P b ω hhits⟩
  intro g
  exact (markedBlockEdges_copy_capacity g P ω c (hcapacity g)).trans hcost

end Erdos911
