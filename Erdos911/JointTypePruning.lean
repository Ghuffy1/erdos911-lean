import Erdos911.StarTypePruning

namespace Erdos911

noncomputable def repeatedTypeCountBoundForEdges (k a j D M R : ℕ) : ℝ :=
  ((D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j)) : ℕ) : ℝ)

noncomputable def repeatedTypeCountBound (k a j D M q : ℕ) : ℝ :=
  repeatedTypeCountBoundForEdges k a j D M (q * q)

noncomputable def jointBadSupport {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (blocks : Finset (RectangleBlock W)) (j s P : ℕ) (L : ℝ) (t : ComponentType G) : Finset (Sym2 W) :=
  repeatedBadSupport G H blocks j t ∪ starBadSupport G H J s P L t

/-- One component type can be chosen for both pruning tests by averaging
the union of their supports over the same class. -/
theorem exists_joint_type_small_support_of_bounded {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (blocks : Finset (RectangleBlock W)) (R : ℕ) (hblocks : BoundedEdgeBlocks blocks R)
    (j s k a D P : ℕ) (L : ℝ) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k a).Nonempty) :
    ∃ t ∈ componentClass G k a, ((jointBadSupport G H J blocks j s P L t).card : ℝ) *
        (componentClass G k a).card ≤ H.edgeFinset.card *
      (repeatedTypeCountBoundForEdges k a j D (P * k) R + starBadTypeBound s k a D P L) := by
  classical
  have hrepeat : ∀ e ∈ H.edgeFinset,
      (((componentClass G k a).filter (fun t => e ∈ repeatedBadSupport G H blocks j t)).card : ℝ) ≤
        repeatedTypeCountBoundForEdges k a j D (P * k) R := by
    intro e _
    have hcount := (Finset.card_le_card (repeatedBadSupport_incidence_subset G H blocks k a j e)).trans
      (repeatedBadTypes_card_le_of_bounded G H e.out.1 blocks R hblocks k a j D (P * k) hD (by
        intro U hUk
        rw [← inducedHostEdges_card]
        exact hlocal U hUk))
    dsimp only [repeatedTypeCountBoundForEdges]
    exact_mod_cast (by simpa only [Nat.mul_assoc] using hcount)
  have hstar : ∀ e ∈ H.edgeFinset,
      (((componentClass G k a).filter (fun t => e ∈ starBadSupport G H J s P L t)).card : ℝ) ≤
        starBadTypeBound s k a D P L := by
    intro e _
    have hsub : (((componentClass G k a).filter (fun t => e ∈ starBadSupport G H J s P L t)).card : ℝ) ≤
        (starBadTypes G H J e.out.1 s k a P L).card := by
      exact_mod_cast Finset.card_le_card (starBadSupport_incidence_subset G H J s k a P L e)
    exact hsub.trans (starBadTypes_card_bound G H J e.out.1 s k a D P L ha hP hD hlocal)
  exact exists_two_supports_small (componentClass G k a) H.edgeFinset
    (repeatedBadSupport G H blocks j) (starBadSupport G H J s P L) hclass
    (fun t _ => repeatedBadSupport_subset G H blocks j t)
    (fun t _ => starBadSupport_subset G H J s P L t)
    (repeatedTypeCountBoundForEdges k a j D (P * k) R) (starBadTypeBound s k a D P L) hrepeat hstar

theorem exists_joint_type_small_support {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (blocks : Finset (RectangleBlock W)) (q : ℕ) (ρ : ℝ) (hblocks : ValidBlockPacking H q ρ blocks)
    (j s k a D P : ℕ) (L : ℝ) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k a).Nonempty) :
    ∃ t ∈ componentClass G k a, ((jointBadSupport G H J blocks j s P L t).card : ℝ) *
        (componentClass G k a).card ≤ H.edgeFinset.card *
      (repeatedTypeCountBound k a j D (P * k) q + starBadTypeBound s k a D P L) := by
  exact exists_joint_type_small_support_of_bounded G H J blocks (q * q)
    hblocks.boundedEdgeBlocks j s k a D P L ha hP hD hlocal hclass

theorem jointBadSupport_eliminates_bad_copies {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (blocks : Finset (RectangleBlock W)) (j s P : ℕ) (L : ℝ) (t : ComponentType G)
    (hsize : 0 < componentSize G t) :
    ∀ f : (componentModel G t).Copy
        (H.deleteEdges (jointBadSupport G H J blocks j s P L t : Set (Sym2 W))),
      (¬3 * j ≤ repeatedEdgeVolume blocks (copyRawEdges
        ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))) ∧
      ¬IsStarDeficitImage H J
        (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
        (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) s P L := by
  classical
  intro f
  let K := H.deleteEdges (jointBadSupport G H J blocks j s P L t : Set (Sym2 W))
  have hKR : K ≤ H.deleteEdges (repeatedBadSupport G H blocks j t : Set (Sym2 W)) := by
    apply H.deleteEdges_anti
    intro e he
    exact Finset.mem_union_left _ he
  have hKS : K ≤ H.deleteEdges (starBadSupport G H J s P L t : Set (Sym2 W)) := by
    apply H.deleteEdges_anti
    intro e he
    exact Finset.mem_union_right _ he
  have hrepeat := repeatedBadSupport_eliminates_bad_copies G H blocks j t hsize
    ((SimpleGraph.Copy.ofLE K _ hKR).comp f)
  have hstar := starBadSupport_eliminates_bad_copies G H J s P L t hsize
    ((SimpleGraph.Copy.ofLE K _ hKS).comp f)
  constructor
  · simpa only [copyRawEdges_ofLE_comp] using hrepeat
  · simpa only [copyVertices_ofLE_comp, copyRawEdges_ofLE_comp] using hstar

theorem exists_joint_pruned_type_of_bounded {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (blocks : Finset (RectangleBlock W)) (R : ℕ) (hblocks : BoundedEdgeBlocks blocks R)
    (j s k a D P : ℕ) (L η E : ℝ) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k a).Nonempty)
    (hbudget : H.edgeFinset.card *
      (repeatedTypeCountBoundForEdges k a j D (P * k) R + starBadTypeBound s k a D P L) ≤
        η * E * (componentClass G k a).card) :
    ∃ t ∈ componentClass G k a, ((jointBadSupport G H J blocks j s P L t).card : ℝ) ≤ η * E ∧
      ∀ f : (componentModel G t).Copy
          (H.deleteEdges (jointBadSupport G H J blocks j s P L t : Set (Sym2 W))),
        (¬3 * j ≤ repeatedEdgeVolume blocks (copyRawEdges
          ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))) ∧
        ¬IsStarDeficitImage H J
          (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
          (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) s P L := by
  classical
  obtain ⟨t, ht, hsmall⟩ := exists_joint_type_small_support_of_bounded G H J blocks R hblocks
    j s k a D P L ha hP hD hlocal hclass
  have hpositive : (0 : ℝ) < (componentClass G k a).card := by exact_mod_cast hclass.card_pos
  have hcost : ((jointBadSupport G H J blocks j s P L t).card : ℝ) ≤ η * E := by
    nlinarith only [hsmall.trans hbudget, hpositive]
  have hsize : 0 < componentSize G t := by
    have hta := (Finset.mem_filter.mp ht).2.2
    omega
  exact ⟨t, ht, hcost, jointBadSupport_eliminates_bad_copies G H J blocks j s P L t hsize⟩

theorem exists_joint_pruned_type {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (blocks : Finset (RectangleBlock W)) (q : ℕ) (ρ : ℝ) (hblocks : ValidBlockPacking H q ρ blocks)
    (j s k a D P : ℕ) (L η E : ℝ) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k a).Nonempty)
    (hbudget : H.edgeFinset.card *
      (repeatedTypeCountBound k a j D (P * k) q + starBadTypeBound s k a D P L) ≤
        η * E * (componentClass G k a).card) :
    ∃ t ∈ componentClass G k a, ((jointBadSupport G H J blocks j s P L t).card : ℝ) ≤ η * E ∧
      ∀ f : (componentModel G t).Copy
          (H.deleteEdges (jointBadSupport G H J blocks j s P L t : Set (Sym2 W))),
        (¬3 * j ≤ repeatedEdgeVolume blocks (copyRawEdges
          ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))) ∧
        ¬IsStarDeficitImage H J
          (copyVertices ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))
          (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) s P L := by
  exact exists_joint_pruned_type_of_bounded G H J blocks (q * q)
    hblocks.boundedEdgeBlocks j s k a D P L η E ha hP hD hlocal hclass hbudget

end Erdos911
