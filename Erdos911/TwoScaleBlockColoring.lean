import Erdos911.TwoScaleBlockCapacity

namespace Erdos911

/-- The block-rich branch of the two-scale coloring argument. After the
repeated-copy pruning, the marked edge set has an explicit capacity budget
for the full target and leaves every connected test copy block-poor. -/
theorem two_scale_block_rich_branch_ambient {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U)
    (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hF : F.Connected)
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (ρ₁ ρ₂ σ : ℝ)
    (hP : ValidBlockPacking K q₁ ρ₁ P) (hQ : ValidBlockPacking K q₂ ρ₂ Q)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q))
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hσ : 0 ≤ σ)
    (b j d D : ℕ) (hd : 4 ≤ d) (hdk : d ≤ Fintype.card V) (hD : 2 ≤ D)
    (hq₁D : q₁ ≤ D) (hq₂D : q₂ ≤ D) (haverage : d * Fintype.card V ≤ 2 * b)
    (hhost : ∀ w, H.degree w ≤ D) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hscale : 32 * Real.log D ≤ p * d)
    (hlocal : ∀ S : Finset U, S.card ≤ 2 * max q₁ q₂ →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hrepeated : ∀ f : F.Copy H, repeatedEdgeVolume (P ∪ Q) (copyRawEdges f) < 3 * j) :
    ∃ marked : Finset (Sym2 W),
      (∀ g : G.Copy K, ((copyRawEdges g ∩ marked).card : ℝ) ≤
        (2 * p) * (2 * σ * K.edgeFinset.card / (ρ₁ * q₁) +
          2 * σ * K.edgeFinset.card / (ρ₂ * q₂))) ∧
      ∀ f : F.Copy (H.deleteEdges (marked : Set (Sym2 W))),
        (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) ∩
          blockEdgeUnion (P ∪ Q)).card < b + 3 * j := by
  have hblocks : BoundedEdgeBlocks (P ∪ Q) (max (q₁ * q₁) (q₂ * q₂)) :=
    hP.boundedEdgeBlocks.union hQ.boundedEdgeBlocks hcross
  have hsquare (q : ℕ) (hqD : q ≤ D) : q * q ≤ D ^ Fintype.card V := by
    calc
      q * q ≤ D * D := Nat.mul_le_mul hqD hqD
      _ = D ^ 2 := (pow_two D).symm
      _ ≤ D ^ Fintype.card V := Nat.pow_le_pow_right (by omega) (by omega)
  have hM : max (q₁ * q₁) (q₂ * q₂) ≤ D ^ Fintype.card V :=
    max_le (hsquare q₁ hq₁D) (hsquare q₂ hq₂D)
  have hcapacity (g : G.Copy K) (B : ↥(P ∪ Q)) :
      ((copyRawEdges g ∩ B.val.edges).card : ℝ) ≤ twoScaleBlockCapacity P Q q₁ q₂ σ B :=
    twoScaleBlockCapacity_bounds_copies G K P Q q₁ q₂ ρ₁ ρ₂ σ hP hQ hσ hlocal g B
  have hdpos : 0 < d := by omega
  have hweights := block_red_weight_bounds (Fintype.card V) b d D
    (max (q₁ * q₁) (q₂ * q₂)) p (hdpos.trans_le hdk) hdpos hdk hD haverage hM hp₀ hscale
  have hparameters := inverse_degree_block_parameters d D p hd hD hscale
  obtain ⟨ω, hcost, hhits⟩ := exists_block_marks_with_budget F H hF (P ∪ Q)
    (max (q₁ * q₁) (q₂ * q₂)) hblocks b D hhost p (1 / d) hp₀ hp₁
    hparameters.1 hweights.1 hweights.2 hparameters.2
    (twoScaleBlockCapacity P Q q₁ q₂ σ) (twoScaleBlockCapacity_nonneg P Q q₁ q₂ σ hσ)
  let marked := markedBlockEdges (P ∪ Q) ω
  have hpoor := marked_block_residual_sparse F H (P ∪ Q) b ω hhits
  refine ⟨marked, ?_, ?_⟩
  · intro g
    have hbudget := (markedBlockEdges_copy_capacity g (P ∪ Q) ω
      (twoScaleBlockCapacity P Q q₁ q₂ σ) (hcapacity g)).trans hcost
    exact hbudget.trans (mul_le_mul_of_nonneg_left
      (twoScaleBlockCapacity_total_bound K P Q q₁ q₂ ρ₁ ρ₂ σ hP hQ hcross
        hq₁ hq₂ hρ₁ hρ₂ hσ) (by positivity))
  · intro f
    let fH : F.Copy H := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
    have hused := block_edges_le_touched_add_repeated (P ∪ Q) hblocks.2 (copyRawEdges fH)
    have htouch : (touchedBlocks (P ∪ Q) (copyRawEdges fH)).card < b := hpoor f
    have hrepeat := hrepeated fH
    change (copyRawEdges fH ∩ blockEdgeUnion (P ∪ Q)).card < b + 3 * j
    omega

theorem two_scale_block_rich_branch {V U W : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (G : SimpleGraph U)
    (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (hF : F.Connected)
    (P Q : Finset (RectangleBlock W)) (q₁ q₂ : ℕ) (ρ₁ ρ₂ σ : ℝ)
    (hP : ValidBlockPacking K q₁ ρ₁ P) (hQ : ValidBlockPacking K q₂ ρ₂ Q)
    (hcross : Disjoint (blockEdgeUnion P) (blockEdgeUnion Q))
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hσ : 0 ≤ σ)
    (b j d D : ℕ) (hd : 4 ≤ d) (hdk : d ≤ Fintype.card V) (hD : 2 ≤ D)
    (hq₁D : q₁ ≤ D) (hq₂D : q₂ ≤ D) (haverage : d * Fintype.card V ≤ 2 * b)
    (hhost : ∀ w, H.degree w ≤ D) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hscale : 32 * Real.log D ≤ p * d)
    (hlocal : ∀ S : Finset U, S.card ≤ 2 * max q₁ q₂ →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hrepeated : ∀ f : F.Copy H, repeatedEdgeVolume (P ∪ Q) (copyRawEdges f) < 3 * j) :
    ∃ marked : Finset (Sym2 W),
      (∀ g : G.Copy H, ((copyRawEdges g ∩ marked).card : ℝ) ≤
        (2 * p) * (2 * σ * K.edgeFinset.card / (ρ₁ * q₁) +
          2 * σ * K.edgeFinset.card / (ρ₂ * q₂))) ∧
      ∀ f : F.Copy (H.deleteEdges (marked : Set (Sym2 W))),
        (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) ∩
          blockEdgeUnion (P ∪ Q)).card < b + 3 * j := by
  obtain ⟨marked, hcapacity, hpoor⟩ := two_scale_block_rich_branch_ambient F G H K hF
    P Q q₁ q₂ ρ₁ ρ₂ σ hP hQ hcross hq₁ hq₂ hρ₁ hρ₂ hσ b j d D hd hdk hD
    hq₁D hq₂D haverage hhost p hp₀ hp₁ hscale hlocal hrepeated
  refine ⟨marked, ?_, hpoor⟩
  intro g
  simpa only [copyRawEdges_ofLE_comp] using hcapacity ((SimpleGraph.Copy.ofLE H K hHK).comp g)

end Erdos911
