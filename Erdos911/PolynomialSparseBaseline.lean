import Erdos911.BaselineRepeatedPruning
import Erdos911.RelabelBlockColoring

namespace Erdos911

/-- The logarithmic baseline for polynomial-degree targets with the
specified local density bound. The threshold is uniform in graph order. -/
theorem polynomial_sparse_baseline (B : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) →
      (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      (∀ S : Finset (Fin n), S.card ≤ 2 * baselineBlockSize d →
        ((G.induce (S : Set (Fin n))).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      baselineHostMultiplier d * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨d₁, hd₁⟩ := polynomial_sparse_block_coloring_general (B + 3) C hC
  obtain ⟨d₂, hd₂⟩ := baseline_repeated_type_pruning B
  obtain ⟨d₃, hd₃⟩ := eventually_baseline_host_parameters
  refine ⟨max d₁ (max d₂ d₃), ?_⟩
  intro d hd n G hn hmin hmax hlocal
  classical
  have hd₁' : d₁ ≤ d := (le_max_left _ _).trans hd
  have hd₂' : d₂ ≤ d := (le_max_left _ _).trans ((le_max_right _ _).trans hd)
  have hd₃' : d₃ ≤ d := (le_max_right _ _).trans ((le_max_right _ _).trans hd)
  obtain ⟨hdlarge, hlog, _, hΛ₀, hΛ₁⟩ := hd₃ d hd₃'
  have hdpos : 0 < d := by omega
  have hΛpos : 0 < baselineHostMultiplier d := by linarith
  have hmin' : ∀ v, d ≤ G.degree v := by simpa only [G.ncard_neighborSet] using hmin
  have hmax' : ∀ v, G.degree v ≤ d ^ B := by simpa only [G.ncard_neighborSet] using hmax
  have hpower : d ≤ d ^ B := (hmin' ⟨0, hn⟩).trans (hmax' ⟨0, hn⟩)
  by_contra hnot
  have hcheap : (SimpleGraph.sizeRamsey G G : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard :=
    le_of_not_gt hnot
  obtain ⟨m, K, hKsize, hRamsey⟩ := sizeRamsey_attained G G
  have hKbudget : (K.edgeFinset.card : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard, hKsize] using hcheap
  obtain ⟨J, hJK, hJdegree, hJdensity, hJcost⟩ := baseline_bounded_sparse_host G K B d
    (by omega) (by linarith) hΛ₀ hΛ₁ hpower hmax' hcheap hKbudget
  obtain ⟨P, hP, hresidual⟩ := exists_dense_block_packing J (baselineBlockSize d) (1 / 4) (by norm_num)
  have hJdegree' : ∀ w, J.degree w ≤ d ^ (B + 3) := by
    simpa only [J.ncard_neighborSet] using hJdegree
  obtain ⟨t, hsupport, hgood⟩ := hd₂ d hd₂' (Fin m) n G hn hmin' hmax' hcheap
    J hJdegree' hJdensity P hP.boundedEdgeBlocks
  let F := componentModel G t
  let E := repeatedBadSupport G J P (componentSize G t / 1024) t
  let H := J.deleteEdges (E : Set (Sym2 (Fin m)))
  have hHJ : H ≤ J := J.deleteEdges_le _
  have hHK : H ≤ K := hHJ.trans hJK
  have hF : F.Connected := componentModel_connected G t
  have hFG : F.IsContained G := ⟨SimpleGraph.Copy.induce G (componentRepresentative G t).supp⟩
  have hFmin : ∀ v, d ≤ F.degree v := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using
      (componentModel_degree_bounds G d (d ^ B) hmin' hmax' t v).1
  have hpow : d ^ B ≤ d ^ (B + 3) := Nat.pow_le_pow_right hdpos (by omega)
  have hFmax : ∀ v, F.degree v ≤ d ^ (B + 3) := by
    intro v
    have hv : F.degree v ≤ d ^ B := by
      simpa only [SimpleGraph.ncard_neighborSet] using
        (componentModel_degree_bounds G d (d ^ B) hmin' hmax' t v).2
    exact hv.trans hpow
  have hHdegree : ∀ w, H.degree w ≤ d ^ (B + 3) := fun w =>
    ((SimpleGraph.Copy.ofLE H J hHJ).degree_le w).trans (hJdegree' w)
  have hFcard : F.edgeFinset.card = componentSize G t := by
    simp only [F, componentSize, SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have hrepeated : ∀ f : F.Copy H,
      repeatedEdgeVolume P (copyRawEdges f) < 3 * (F.edgeFinset.card / 1024) := by
    intro f
    rw [hFcard]
    simpa only [copyRawEdges_ofLE_comp] using hgood f
  have hnodense : ∀ S T : Finset (Fin m), S.card = baselineBlockSize d →
      T.card = baselineBlockSize d → Disjoint S T →
      (crossEdges (H.deleteEdges (blockEdgeUnion P : Set (Sym2 (Fin m)))) S T : ℝ) ≤
        (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d := by
    intro S T hS hT hST
    have hmono : (crossEdges (H.deleteEdges (blockEdgeUnion P : Set (Sym2 (Fin m)))) S T : ℝ) ≤
        crossEdges (J.deleteEdges (blockEdgeUnion P : Set (Sym2 (Fin m)))) S T := by
      exact_mod_cast crossEdges_mono (SimpleGraph.deleteEdges_mono hHJ) S T
    exact hmono.trans (hresidual S T hS hT hST)
  have hE : (E.card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 16 := by
    have hJedges : (J.edgeFinset.card : ℝ) ≤ K.edgeFinset.card := by
      exact_mod_cast Finset.card_le_card (SimpleGraph.edgeFinset_mono hJK)
    calc
      (E.card : ℝ) ≤ J.edgeFinset.card / (16 * baselineHostMultiplier d) := hsupport
      _ ≤ K.edgeFinset.card / (16 * baselineHostMultiplier d) :=
        div_le_div_of_nonneg_right hJedges (by positivity)
      _ ≤ (baselineHostMultiplier d * G.edgeSet.ncard) / (16 * baselineHostMultiplier d) :=
        div_le_div_of_nonneg_right hKbudget (by positivity)
      _ = (G.edgeSet.ncard : ℝ) / 16 := by field_simp
  have hdeleted : ∀ g : G.Copy K,
      ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4 := by
    intro g
    have hcost : ((copyRawEdges g ∩ (K \ J).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 8 := by
      have heq : (K \ J).edgeSet.toFinite.toFinset = (K \ J).edgeFinset := by
        ext e
        simp only [Set.Finite.mem_toFinset, SimpleGraph.mem_edgeFinset]
      simpa only [heq] using hJcost g
    have hsum : ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤
        (copyRawEdges g ∩ (K \ J).edgeFinset).card + E.card := by
      exact_mod_cast copy_deleted_capacity_delete G K J E g
    nlinarith [Nat.cast_nonneg (α := ℝ) G.edgeSet.ncard]
  obtain ⟨R, hRK, hred, hblue⟩ := hd₁ d hd₁' (componentRepresentative G t).supp (Fin n) (Fin m)
    F G H K hF hFG hHK (d ^ (B + 3)) hFmin hFmax hHdegree le_rfl hKbudget hlocal
    P (hP.mono hJK) hrepeated hnodense hdeleted
  exact (hRamsey R hRK).elim hred hblue

end Erdos911
