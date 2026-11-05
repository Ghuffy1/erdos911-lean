import Erdos911.OnePoolPatterns
import Erdos911.HighLowHost
import Erdos911.InducedHostEdges

namespace Erdos911

noncomputable def lowVertexSubsets {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (T : ℕ) (U : Finset W) (a : ℕ) :
    Finset (Finset W) := by
  classical
  exact U.powerset.filter (fun A => A.card ≤ a ∧ ∀ x ∈ A, K.degree x ≤ T)

theorem mem_lowVertexSubsets {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (T : ℕ) (U A : Finset W) (a : ℕ) :
    A ∈ lowVertexSubsets K T U a ↔ A ⊆ U ∧ A.card ≤ a ∧ ∀ x ∈ A, K.degree x ≤ T := by
  classical
  simp only [lowVertexSubsets, Finset.mem_filter, Finset.mem_powerset]

theorem lowVertexSubsets_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] (T : ℕ) (U : Finset W) (a : ℕ) :
    (lowVertexSubsets K T U a).card ≤ 2 ^ U.card := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powerset U)

noncomputable def orientationPatterns {W : Type*} [Fintype W] [DecidableEq W]
    (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T : ℕ) (U : Finset W) (a e : ℕ) (g : ℝ) : Finset (Finset (Sym2 W)) :=
  (lowVertexSubsets K T U a).biUnion (fun A =>
    onePoolPatterns (inducedHostEdges H U) (incidentEdgesAtSet H A) e g)

theorem mem_orientationPatterns {W : Type*} [Fintype W] [DecidableEq W]
    (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T : ℕ) (U : Finset W) (a e : ℕ) (g : ℝ) (E : Finset (Sym2 W)) :
    E ∈ orientationPatterns H K T U a e g ↔
      ∃ A ⊆ U, A.card ≤ a ∧ (∀ x ∈ A, K.degree x ≤ T) ∧
        E ⊆ inducedHostEdges H U ∧ E.card = e ∧ g ≤ (E ∩ incidentEdgesAtSet H A).card := by
  classical
  simp only [orientationPatterns, Finset.mem_biUnion, mem_lowVertexSubsets, mem_onePoolPatterns]
  aesop

/-- Low left images lie in a pool of at most `T*a` edges, while the
whole image has at most `T*k` edges. The entropy saving is `g*log(k/a)`. -/
theorem orientationPatterns_card_bound {W : Type*} [Fintype W] [DecidableEq W]
    (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj] (hHK : H ≤ K)
    (T : ℕ) (U : Finset W) (a e : ℕ) (g : ℝ)
    (hT : 0 < T) (ha : 0 < a) (he : 0 < e) (haU : a ≤ U.card)
    (hU : (inducedHostEdges H U).card ≤ T * U.card) :
    ((orientationPatterns H K T U a e g).card : ℝ) ≤
      (2 : ℝ) ^ U.card * (e + 1 : ℝ) *
        Real.exp ((e : ℝ) * Real.log ((T * U.card : ℝ) / e) -
          g * Real.log ((U.card : ℝ) / a) + 2 * e) := by
  classical
  let Z := lowVertexSubsets K T U a
  let Q := fun A => onePoolPatterns (inducedHostEdges H U) (incidentEdgesAtSet H A) e g
  let b := (e + 1 : ℝ) * Real.exp ((e : ℝ) * Real.log ((T * U.card : ℝ) / e) -
    g * Real.log ((U.card : ℝ) / a) + 2 * e)
  have hratio : (T : ℝ) * U.card / ((T : ℝ) * a) = (U.card : ℝ) / a := by
    have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp
  have hbound (A : Finset W) (hA : A ∈ Z) : ((Q A).card : ℝ) ≤ b := by
    obtain ⟨_, hAa, hAlow⟩ := (mem_lowVertexSubsets K T U A a).mp hA
    have hdegree : ∀ x ∈ A, H.degree x ≤ T := fun x hx =>
      ((SimpleGraph.Copy.ofLE H K hHK).degree_le x).trans (hAlow x hx)
    have hpool : (incidentEdgesAtSet H A).card ≤ T * a := by
      calc
        _ ≤ A.card * T := incidentEdgesAtSet_card_le_on H A T hdegree
        _ ≤ a * T := Nat.mul_le_mul_right T hAa
        _ = T * a := Nat.mul_comm _ _
    have h := onePoolPatterns_card_bound (inducedHostEdges H U) (incidentEdgesAtSet H A)
      e (T * a) (T * U.card) g he (Nat.mul_pos hT ha) (Nat.mul_le_mul_left T haU) hU hpool
    simp only [Nat.cast_mul] at h
    simpa only [Q, b, hratio] using h
  have hZ : (Z.card : ℝ) ≤ (2 : ℝ) ^ U.card := by
    exact_mod_cast lowVertexSubsets_card_le K T U a
  calc
    ((orientationPatterns H K T U a e g).card : ℝ) ≤ ∑ A ∈ Z, ((Q A).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Z) (t := Q))
    _ ≤ ∑ _A ∈ Z, b := Finset.sum_le_sum hbound
    _ = Z.card * b := by simp
    _ ≤ (2 : ℝ) ^ U.card * b := mul_le_mul_of_nonneg_right hZ (by dsimp only [b]; positivity)
    _ = _ := by dsimp only [b]; ring

theorem copy_mem_orientationPatterns {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (f : F.Copy H) (left : Finset V) (T a : ℕ) (g : ℝ) (ha : left.card ≤ a)
    (hmass : g ≤ (copyRawEdges f ∩ incidentEdgesAtSet H
      ((left.filter (fun v => f v ∉ highHostVertices K T)).image f)).card) :
    copyRawEdges f ∈ orientationPatterns H K T (copyVertices f) a F.edgeSet.ncard g := by
  classical
  let A := (left.filter (fun v => f v ∉ highHostVertices K T)).image f
  apply (mem_orientationPatterns H K T (copyVertices f) a F.edgeSet.ncard g (copyRawEdges f)).mpr
  refine ⟨A, ?_, ?_, ?_, copyRawEdges_subset_inducedHostEdges f, copyRawEdges_card f, hmass⟩
  · intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  · exact (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans ha
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.le_of_not_gt (fun h => (Finset.mem_filter.mp hv).2 ((mem_highHostVertices K T (f v)).mpr h))

end Erdos911
