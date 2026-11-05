import Erdos911.ImagePatternPruning
import Erdos911.OrientationPruning
import Erdos911.JointTypePruning

namespace Erdos911

theorem exists_three_supports_small {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (R P Q : A → Finset B)
    (hS : S.Nonempty) (hR : ∀ a ∈ S, R a ⊆ T) (hP : ∀ a ∈ S, P a ⊆ T)
    (hQ : ∀ a ∈ S, Q a ⊆ T) (CR CP CQ : ℝ)
    (hCR : ∀ b ∈ T, ((S.filter (fun a => b ∈ R a)).card : ℝ) ≤ CR)
    (hCP : ∀ b ∈ T, ((S.filter (fun a => b ∈ P a)).card : ℝ) ≤ CP)
    (hCQ : ∀ b ∈ T, ((S.filter (fun a => b ∈ Q a)).card : ℝ) ≤ CQ) :
    ∃ a ∈ S, (((R a ∪ P a) ∪ Q a).card : ℝ) * S.card ≤ T.card * ((CR + CP) + CQ) := by
  classical
  apply exists_two_supports_small S T (fun a => R a ∪ P a) Q hS
    (fun a ha => Finset.union_subset (hR a ha) (hP a ha)) hQ (CR + CP) CQ ?_ hCQ
  intro b hb
  have hfilter : S.filter (fun a => b ∈ R a ∪ P a) =
      S.filter (fun a => b ∈ R a) ∪ S.filter (fun a => b ∈ P a) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union, and_or_left]
  have hcard : ((S.filter (fun a => b ∈ R a ∪ P a)).card : ℝ) ≤
      (S.filter (fun a => b ∈ R a)).card + (S.filter (fun a => b ∈ P a)).card := by
    rw [hfilter]
    exact_mod_cast Finset.card_union_le (S.filter (fun a => b ∈ R a)) (S.filter (fun a => b ∈ P a))
  linarith only [hcard, hCR b hb, hCP b hb]

theorem imageStarPatternSupport_incidence_bound {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s k m D P : ℕ) (ℓ : ℝ) (hm : 0 < m) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (e : Sym2 W) :
    (((componentClass G k m).filter (fun t => e ∈ imagePatternBadSupport G H
      (fun U => starImagePatterns H J U s m D P ℓ) t)).card : ℝ) ≤ starBadTypeBound s k m D P ℓ := by
  let b : ℝ := (((D ^ 2 + 1) ^ (s * k) : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) ^ k *
    Real.exp ((m : ℝ) * Real.log ((P * k : ℝ) / m) - ℓ + 2 * m)
  have h := imagePatternBadSupport_incidence_bound G H
    (fun U => starImagePatterns H J U s m D P ℓ) k m D b hD (by dsimp only [b]; positivity) (by
      intro U hUk hU
      simpa only [hUk, b] using starImagePatterns_card_bound H J U s m D P ℓ hU hm hP hD
        (by simpa only [hUk] using hlocal U hUk)) e
  simpa only [b, starBadTypeBound, mul_assoc] using h

noncomputable def incidenceJointBadSupport {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj]
    (blocks : Finset (RectangleBlock W)) (j s D P a m : ℕ) (g ℓ : ℝ)
    (t : ComponentType G) : Finset (Sym2 W) :=
  (orientationBadSupport G H K P a g t ∪ repeatedBadSupport G H blocks j t) ∪
    imagePatternBadSupport G H (fun U => starImagePatterns H J U s m D P ℓ) t

/-- The orientation, repeated-block and fractional-star tests all use
one selected component type and one combined deleted-edge allowance. -/
theorem exists_incidence_joint_type_small_support {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj] (hHK : H ≤ K)
    (blocks : Finset (RectangleBlock W)) (R : ℕ) (hblocks : BoundedEdgeBlocks blocks R)
    (j s k a m D P : ℕ) (g ℓ : ℝ) (ha : 0 < a) (hm : 0 < m) (hP : 0 < P) (hak : a ≤ k)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k m).Nonempty) :
    ∃ t ∈ componentClass G k m,
      ((incidenceJointBadSupport G H J K blocks j s D P a m g ℓ t).card : ℝ) *
        (componentClass G k m).card ≤ H.edgeFinset.card *
          ((orientationBadTypeBound P k a m D g + repeatedTypeCountBoundForEdges k m j D (P * k) R) +
            starBadTypeBound s k m D P ℓ) := by
  classical
  apply exists_three_supports_small (componentClass G k m) H.edgeFinset
    (orientationBadSupport G H K P a g) (repeatedBadSupport G H blocks j)
    (imagePatternBadSupport G H (fun U => starImagePatterns H J U s m D P ℓ)) hclass
    (fun t _ => orientationBadSupport_subset G H K P a g t)
    (fun t _ => repeatedBadSupport_subset G H blocks j t)
    (fun t _ => imagePatternBadSupport_subset G H _ t) _ _ _ ?_ ?_ ?_
  · intro e _
    have h := Finset.card_le_card (orientationBadSupport_incidence_subset G H K P k a m g e)
    have h' := orientationBadTypes_card_bound G H K hHK e.out.1 P k a m D g hP ha hm hak hD hlocal
    exact (show (((componentClass G k m).filter
      (fun t => e ∈ orientationBadSupport G H K P a g t)).card : ℝ) ≤
        (orientationBadTypes G H K e.out.1 P k a m g).card by exact_mod_cast h).trans h'
  · intro e _
    have h := (Finset.card_le_card (repeatedBadSupport_incidence_subset G H blocks k m j e)).trans
      (repeatedBadTypes_card_le_of_bounded G H e.out.1 blocks R hblocks k m j D (P * k) hD (by
        intro U hUk
        rw [← inducedHostEdges_card]
        exact hlocal U hUk))
    dsimp only [repeatedTypeCountBoundForEdges]
    exact_mod_cast (by simpa only [Nat.mul_assoc] using h)
  · intro e _
    exact imageStarPatternSupport_incidence_bound G H J s k m D P ℓ hm hP hD hlocal e

theorem incidenceJointBadSupport_eliminates_bad_copies {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj]
    (blocks : Finset (RectangleBlock W)) (j s D P a m : ℕ) (g ℓ : ℝ)
    (t : ComponentType G) (hsize : 0 < componentSize G t) :
    ∀ f : (componentModel G t).Copy
      (H.deleteEdges (incidenceJointBadSupport G H J K blocks j s D P a m g ℓ t : Set (Sym2 W))),
      let fH := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
      (copyRawEdges fH ∉ orientationPatterns H K P (copyVertices fH) a (componentSize G t) g) ∧
        (¬3 * j ≤ repeatedEdgeVolume blocks (copyRawEdges fH)) ∧
        copyRawEdges fH ∉ starImagePatterns H J (copyVertices fH) s m D P ℓ := by
  classical
  intro f
  let B := incidenceJointBadSupport G H J K blocks j s D P a m g ℓ t
  let H' := H.deleteEdges (B : Set (Sym2 W))
  have hO : H' ≤ H.deleteEdges (orientationBadSupport G H K P a g t : Set (Sym2 W)) := by
    apply H.deleteEdges_anti
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  have hR : H' ≤ H.deleteEdges (repeatedBadSupport G H blocks j t : Set (Sym2 W)) := by
    apply H.deleteEdges_anti
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_right _ he)
  have hS : H' ≤ H.deleteEdges (imagePatternBadSupport G H
      (fun U => starImagePatterns H J U s m D P ℓ) t : Set (Sym2 W)) := by
    apply H.deleteEdges_anti
    intro e he
    exact Finset.mem_union_right _ he
  have ho := orientationBadSupport_eliminates_bad_copies G H K P a g t hsize
    ((SimpleGraph.Copy.ofLE H' _ hO).comp f)
  have hr := repeatedBadSupport_eliminates_bad_copies G H blocks j t hsize
    ((SimpleGraph.Copy.ofLE H' _ hR).comp f)
  have hs := imagePatternBadSupport_eliminates_bad_copies G H
    (fun U => starImagePatterns H J U s m D P ℓ) t hsize ((SimpleGraph.Copy.ofLE H' _ hS).comp f)
  exact ⟨by simpa only [copyRawEdges_ofLE_comp, copyVertices_ofLE_comp] using ho,
    by simpa only [copyRawEdges_ofLE_comp] using hr,
    by simpa only [copyRawEdges_ofLE_comp, copyVertices_ofLE_comp] using hs⟩

theorem exists_incidence_joint_pruned_type {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J K : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] [DecidableRel K.Adj] (hHK : H ≤ K)
    (blocks : Finset (RectangleBlock W)) (R : ℕ) (hblocks : BoundedEdgeBlocks blocks R)
    (j s k a m D P : ℕ) (g ℓ η E : ℝ) (ha : 0 < a) (hm : 0 < m) (hP : 0 < P) (hak : a ≤ k)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k)
    (hclass : (componentClass G k m).Nonempty)
    (hbudget : H.edgeFinset.card *
      ((orientationBadTypeBound P k a m D g + repeatedTypeCountBoundForEdges k m j D (P * k) R) +
        starBadTypeBound s k m D P ℓ) ≤ η * E * (componentClass G k m).card) :
    ∃ t ∈ componentClass G k m,
      ((incidenceJointBadSupport G H J K blocks j s D P a m g ℓ t).card : ℝ) ≤ η * E ∧
      ∀ f : (componentModel G t).Copy
        (H.deleteEdges (incidenceJointBadSupport G H J K blocks j s D P a m g ℓ t : Set (Sym2 W))),
        let fH := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
        (copyRawEdges fH ∉ orientationPatterns H K P (copyVertices fH) a (componentSize G t) g) ∧
          (¬3 * j ≤ repeatedEdgeVolume blocks (copyRawEdges fH)) ∧
          copyRawEdges fH ∉ starImagePatterns H J (copyVertices fH) s m D P ℓ := by
  classical
  obtain ⟨t, ht, hsmall⟩ := exists_incidence_joint_type_small_support G H J K hHK blocks R hblocks
    j s k a m D P g ℓ ha hm hP hak hD hlocal hclass
  have hpositive : (0 : ℝ) < (componentClass G k m).card := by exact_mod_cast hclass.card_pos
  have hcost : ((incidenceJointBadSupport G H J K blocks j s D P a m g ℓ t).card : ℝ) ≤ η * E := by
    nlinarith only [hsmall.trans hbudget, hpositive]
  have hsize : 0 < componentSize G t := by
    have htm := (Finset.mem_filter.mp ht).2.2
    omega
  exact ⟨t, ht, hcost, incidenceJointBadSupport_eliminates_bad_copies G H J K blocks
    j s D P a m g ℓ t hsize⟩

end Erdos911
