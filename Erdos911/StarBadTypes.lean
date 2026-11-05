import Erdos911.StarImagePatterns
import Erdos911.ComponentModels

namespace Erdos911

noncomputable def IsStarBadType {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (root : W) (s k a P : ℕ) (L : ℝ) (t : ComponentType G) : Prop :=
  componentOrder G t = k ∧ componentSize G t = a ∧
    ∃ f : (componentModel G t).Copy H, root ∈ copyVertices f ∧
      IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P L

noncomputable def starBadTypes {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (root : W) (s k a P : ℕ) (L : ℝ) : Finset (ComponentType G) := by
  classical
  exact Finset.univ.filter (IsStarBadType G H J root s k a P L)

noncomputable def starBadTypeBound (s k a D P : ℕ) (L : ℝ) : ℝ :=
  (D ^ (2 * (k - 1)) : ℝ) * (((D ^ 2 + 1) ^ (s * k) : ℕ) : ℝ) *
    ((D + 1 : ℕ) : ℝ) ^ k *
      Real.exp ((a : ℝ) * Real.log ((P * k : ℝ) / a) - L + 2 * a)

/-- Distinct component types with a witnessed star deficit are counted by
their rooted image support and the finite restricted-star descriptions. -/
theorem starBadTypes_card_bound {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (root : W) (s k a D P : ℕ) (L : ℝ) (ha : 0 < a) (hP : 0 < P)
    (hD : ∀ w, H.degree w ≤ D)
    (hlocal : ∀ U : Finset W, U.card = k → (inducedHostEdges H U).card ≤ P * k) :
    ((starBadTypes G H J root s k a P L).card : ℝ) ≤
      starBadTypeBound s k a D P L := by
  classical
  let B := starBadTypes G H J root s k a P L
  let C := rootedConnectedSets H root k
  let patterns := fun U : C => starImagePatterns H J U.val s a D P L
  let bound : ℝ := (((D ^ 2 + 1) ^ (s * k) : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) ^ k *
    Real.exp ((a : ℝ) * Real.log ((P * k : ℝ) / a) - L + 2 * a)
  have hdata : ∀ t : B, IsStarBadType G H J root s k a P L t.val := by
    intro t
    exact (Finset.mem_filter.mp t.property).2
  have hex : ∀ t : B, ∃ f : (componentModel G t.val).Copy H,
      root ∈ copyVertices f ∧ IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P L := by
    intro t
    exact (hdata t).2.2
  choose f hfroot hfbad using hex
  have horder : ∀ t : B, Fintype.card (componentRepresentative G t.val).supp = k := by
    intro t
    simpa only [componentOrder, Nat.card_eq_fintype_card] using (hdata t).1
  have hvertices : ∀ t : B, copyVertices (f t) ∈ C := by
    intro t
    have h := copyVertices_mem_rooted (f t) (componentModel_connected G t.val) root (hfroot t)
    simpa only [horder t] using h
  have hpatterns : ∀ t : B, copyRawEdges (f t) ∈ patterns ⟨copyVertices (f t), hvertices t⟩ := by
    intro t
    apply starDeficitImage_mem_patterns H J (copyVertices (f t)) (copyRawEdges (f t)) s a D P L
      ⟨root, hfroot t⟩ (copyRawEdges_subset_inducedHostEdges (f t))
    · rw [copyRawEdges_card]
      exact (hdata t).2.1
    · exact hD
    · exact hfbad t
  let encode : B → (Σ U : C, patterns U) := fun t =>
    ⟨⟨copyVertices (f t), hvertices t⟩, ⟨copyRawEdges (f t), hpatterns t⟩⟩
  have hinj : Function.Injective encode := by
    intro u v huv
    have hverts := congrArg (fun x : Σ U : C, patterns U => x.1.val) huv
    have hedges := congrArg (fun x : Σ U : C, patterns U => x.2.val) huv
    apply Subtype.ext
    exact (componentModel_iso_iff G u.val v.val).mp (iso_of_copy_images (f u) (f v) hverts hedges)
  have hpatternBound : ∀ U : C, ((patterns U).card : ℝ) ≤ bound := by
    intro U
    have hU := (Finset.mem_filter.mp U.property).2
    have hUk : U.val.card = k := hU.2.1
    simpa only [patterns, bound, hUk] using starImagePatterns_card_bound H J U.val s a D P L
      ⟨root, hU.1⟩ ha hP hD (by simpa only [hUk] using hlocal U.val hUk)
  have hcount : B.card ≤ ∑ U : C, (patterns U).card := by
    have h := Fintype.card_le_of_injective encode hinj
    simpa only [Fintype.card_coe, Fintype.card_sigma] using h
  have hC : (C.card : ℝ) ≤ (D ^ (2 * (k - 1)) : ℝ) := by
    exact_mod_cast rooted_connected_set_count H D hD root k
  calc
    (B.card : ℝ) ≤ ∑ U : C, ((patterns U).card : ℝ) := by exact_mod_cast hcount
    _ ≤ ∑ _U : C, bound := Finset.sum_le_sum (fun U _ => hpatternBound U)
    _ = (C.card : ℝ) * bound := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (D ^ (2 * (k - 1)) : ℝ) * bound := mul_le_mul_of_nonneg_right hC (by dsimp [bound]; positivity)
    _ = _ := by dsimp only [bound, starBadTypeBound]; ring

end Erdos911
