import Erdos911.ComponentModels
import Erdos911.InducedHostEdges
import Erdos911.RepeatedBlockCounting
import Erdos911.BinomialEntropy
import Erdos911.LowEndpointDensity

namespace Erdos911

noncomputable def IsRepeatedBadType {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (root : W)
    (P : Finset (RectangleBlock W)) (k a j : ℕ) (t : ComponentType G) : Prop := by
  classical
  exact componentOrder G t = k ∧ componentSize G t = a ∧
    ∃ f : (componentModel G t).Copy H,
      root ∈ copyVertices f ∧ 3 * j ≤ repeatedEdgeVolume P (copyRawEdges f)

noncomputable def repeatedBadTypes {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (root : W)
    (P : Finset (RectangleBlock W)) (k a j : ℕ) : Finset (ComponentType G) := by
  classical
  exact Finset.univ.filter (IsRepeatedBadType G H root P k a j)

/-- Distinct bad component types inject into a rooted connected vertex
set and an edge subset with a disjoint-pair witness. -/
theorem repeatedBadTypes_card_le_of_bounded {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) (P : Finset (RectangleBlock W)) (R : ℕ)
    (hP : BoundedEdgeBlocks P R) (k a j D M : ℕ)
    (hD : ∀ w, H.degree w ≤ D)
    (hM : ∀ U : Finset W, U.card = k → (H.induce (U : Set W)).edgeSet.ncard ≤ M) :
    (repeatedBadTypes G H root P k a j).card ≤
      D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j)) := by
  classical
  let B := repeatedBadTypes G H root P k a j
  let C := rootedConnectedSets H root k
  let patterns (U : C) := repeatedBlockSubsets P (inducedHostEdges H U.val) a j
  have hdata : ∀ t : B, IsRepeatedBadType G H root P k a j t.val := by
    intro t
    exact (Finset.mem_filter.mp t.property).2
  have hex : ∀ t : B, ∃ f : (componentModel G t.val).Copy H,
      root ∈ copyVertices f ∧ 3 * j ≤ repeatedEdgeVolume P (copyRawEdges f) := by
    intro t
    exact (hdata t).2.2
  choose f hfroot hfrepeat using hex
  have horder : ∀ t : B, Fintype.card (componentRepresentative G t.val).supp = k := by
    intro t
    simpa only [componentOrder, Nat.card_eq_fintype_card] using (hdata t).1
  have hsize : ∀ t : B, (copyRawEdges (f t)).card = a := by
    intro t
    rw [copyRawEdges_card]
    exact (hdata t).2.1
  have hvertices : ∀ t : B, copyVertices (f t) ∈ C := by
    intro t
    have h := copyVertices_mem_rooted (f t) (componentModel_connected G t.val) root (hfroot t)
    simpa only [horder t] using h
  have hedges : ∀ t : B, copyRawEdges (f t) ∈
      patterns ⟨copyVertices (f t), hvertices t⟩ := by
    intro t
    apply (mem_repeatedBlockSubsets P (inducedHostEdges H (copyVertices (f t)))
      (copyRawEdges (f t)) a j).mpr
    exact ⟨copyRawEdges_subset_inducedHostEdges (f t), hsize t, hfrepeat t⟩
  let encode : B → (Σ U : C, patterns U) := fun t =>
    ⟨⟨copyVertices (f t), hvertices t⟩, ⟨copyRawEdges (f t), hedges t⟩⟩
  have hinj : Function.Injective encode := by
    intro s t h
    have hv : copyVertices (f s) = copyVertices (f t) :=
      congrArg (fun p : Σ U : C, patterns U => p.1.val) h
    have he : copyRawEdges (f s) = copyRawEdges (f t) :=
      congrArg (fun p : Σ U : C, patterns U => p.2.val) h
    apply Subtype.ext
    exact (componentModel_iso_iff G s.val t.val).mp (iso_of_copy_images (f s) (f t) hv he)
  have hpatterns : ∀ U : C, (patterns U).card ≤
      (M * R).choose j * M.choose (a - 2 * j) := by
    intro U
    have hUcard : U.val.card = k := (Finset.mem_filter.mp U.property).2.2.1
    have havailable : (inducedHostEdges H U.val).card ≤ M := by
      rw [inducedHostEdges_card]
      exact hM U.val hUcard
    exact (repeatedBlockSubsets_card_le_of_bounded hP (inducedHostEdges H U.val) a j).trans
      (Nat.mul_le_mul (Nat.choose_le_choose j (Nat.mul_le_mul_right _ havailable))
        (Nat.choose_le_choose (a - 2 * j) havailable))
  calc
    B.card = Fintype.card B := (Fintype.card_coe B).symm
    _ ≤ Fintype.card (Σ U : C, patterns U) := Fintype.card_le_of_injective encode hinj
    _ = ∑ U : C, (patterns U).card := by simp only [Fintype.card_sigma, Fintype.card_coe]
    _ ≤ ∑ _U : C, (M * R).choose j * M.choose (a - 2 * j) :=
      Finset.sum_le_sum (fun U _ => hpatterns U)
    _ = C.card * ((M * R).choose j * M.choose (a - 2 * j)) := by simp
    _ ≤ D ^ (2 * (k - 1)) * ((M * R).choose j * M.choose (a - 2 * j)) :=
      Nat.mul_le_mul_right _ (rooted_connected_set_count H D hD root k)

theorem repeatedBadTypes_card_le {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) (P : Finset (RectangleBlock W)) (q : ℕ) (ρ : ℝ)
    (hP : ValidBlockPacking H q ρ P) (k a j D M : ℕ)
    (hD : ∀ w, H.degree w ≤ D)
    (hM : ∀ U : Finset W, U.card = k → (H.induce (U : Set W)).edgeSet.ncard ≤ M) :
    (repeatedBadTypes G H root P k a j).card ≤
      D ^ (2 * (k - 1)) * ((M * (q * q)).choose j * M.choose (a - 2 * j)) := by
  exact repeatedBadTypes_card_le_of_bounded G H root P (q * q)
    hP.boundedEdgeBlocks k a j D M hD hM

theorem repeatedBadTypes_card_le_low_endpoint {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) (P : Finset (RectangleBlock W)) (q : ℕ) (ρ : ℝ)
    (hP : ValidBlockPacking H q ρ P) (k a j D B : ℕ)
    (hD : ∀ w, H.degree w ≤ D)
    (hlow : ∀ u v, H.Adj u v → H.degree u ≤ B ∨ H.degree v ≤ B) :
    (repeatedBadTypes G H root P k a j).card ≤
      D ^ (2 * (k - 1)) * (((B * k) * (q * q)).choose j * (B * k).choose (a - 2 * j)) := by
  apply repeatedBadTypes_card_le G H root P q ρ hP k a j D (B * k) hD
  intro U hU
  simpa only [hU] using induced_edges_le_low_endpoint_degree H B hlow U

/-- The repeated-block entropy estimate for actual component types,
including the cost of their rooted connected image supports. -/
theorem repeatedBadTypes_exp_bound_of_bounded {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) (P : Finset (RectangleBlock W)) (R : ℕ)
    (hP : BoundedEdgeBlocks P R) (k a j D M : ℕ)
    (hD : ∀ w, H.degree w ≤ D)
    (hM : ∀ U : Finset W, U.card = k → (H.induce (U : Set W)).edgeSet.ncard ≤ M)
    (hDpos : 0 < D) (hMpos : 0 < M) (hR : 0 < R) (hja : 2 * j ≤ a) :
    ((repeatedBadTypes G H root P k a j).card : ℝ) ≤
      Real.exp (((2 * (k - 1) : ℕ) : ℝ) * Real.log D +
        (a : ℝ) * Real.log ((M : ℝ) / a) -
        (j : ℝ) * Real.log ((M : ℝ) / ((a : ℝ) * R)) + 2 * a) := by
  have hcount : ((repeatedBadTypes G H root P k a j).card : ℝ) ≤
      (D : ℝ) ^ (2 * (k - 1)) *
        (((M * R).choose j : ℝ) * (M.choose (a - 2 * j) : ℝ)) := by
    exact_mod_cast repeatedBadTypes_card_le_of_bounded G H root P R hP k a j D M hD hM
  have hbin : ((M * R).choose j : ℝ) * (M.choose (a - 2 * j) : ℝ) ≤
      Real.exp ((a : ℝ) * Real.log ((M : ℝ) / a) -
        (j : ℝ) * Real.log ((M : ℝ) / ((a : ℝ) * R)) + 2 * a) := by
    simpa only [Nat.cast_mul] using pair_choose_product_exp_bound M R a j
      hMpos hR hja
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hDpow : (D : ℝ) ^ (2 * (k - 1)) =
      Real.exp (((2 * (k - 1) : ℕ) : ℝ) * Real.log D) := by
    calc
      (D : ℝ) ^ (2 * (k - 1)) = Real.exp (Real.log ((D : ℝ) ^ (2 * (k - 1)))) :=
        (Real.exp_log (pow_pos hDreal _)).symm
      _ = _ := by rw [Real.log_pow]
  apply hcount.trans
  apply (mul_le_mul_of_nonneg_left hbin (pow_nonneg hDreal.le _)).trans
  rw [hDpow, ← Real.exp_add]
  apply le_of_eq
  congr 1
  ring

theorem repeatedBadTypes_exp_bound {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (root : W) (P : Finset (RectangleBlock W)) (q : ℕ) (ρ : ℝ)
    (hP : ValidBlockPacking H q ρ P) (k a j D M : ℕ)
    (hD : ∀ w, H.degree w ≤ D)
    (hM : ∀ U : Finset W, U.card = k → (H.induce (U : Set W)).edgeSet.ncard ≤ M)
    (hDpos : 0 < D) (hMpos : 0 < M) (hq : 0 < q) (hja : 2 * j ≤ a) :
    ((repeatedBadTypes G H root P k a j).card : ℝ) ≤
      Real.exp (((2 * (k - 1) : ℕ) : ℝ) * Real.log D +
        (a : ℝ) * Real.log ((M : ℝ) / a) -
        (j : ℝ) * Real.log ((M : ℝ) / ((a : ℝ) * (q * q))) + 2 * a) := by
  simpa only [Nat.cast_mul] using repeatedBadTypes_exp_bound_of_bounded G H root P
    (q * q) hP.boundedEdgeBlocks k a j D M hD hM hDpos hMpos (Nat.mul_pos hq hq) hja

end Erdos911
