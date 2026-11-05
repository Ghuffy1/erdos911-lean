import Erdos911.EntropyRepeatedPruning
import Erdos911.EntropyBlockBudget
import Erdos911.SparseEntropyColoring
import Erdos911.TripleLogEntropy
import Erdos911.LinearForestError
import Erdos911.RelabelBlockColoring
import Erdos911.PolynomialLowEntropy

namespace Erdos911

/-- A linear-host obstruction under the triple-log entropy threshold.
The minimum-degree threshold is uniform in the order of the target. -/
theorem polynomial_triple_log_entropy_bound (B : ℕ) (M C : ℝ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 0 < n →
      (∀ v, d ≤ (G.neighborSet v).ncard) →
      (∀ v, (G.neighborSet v).ncard ≤ d ^ B) →
      (∀ S : Finset (Fin n), S.card ≤ 2 * baselineBlockSize d →
        ((G.induce (S : Set (Fin n))).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
      componentEntropyMass G ≤ (G.edgeSet.ncard : ℝ) * tripleLogEntropyThreshold d →
      (M * d) * G.edgeSet.ncard < (SimpleGraph.sizeRamsey G G : ℝ) := by
  obtain ⟨d₁, hd₁⟩ := baseline_coloring_parameters_uniform (B + 3)
  obtain ⟨d₂, hd₂⟩ := eventually_entropy_host_parameters B M
  obtain ⟨d₃, hd₃⟩ := entropy_repeated_type_pruning B M hM
  obtain ⟨d₄, hd₄⟩ := eventually_residual_entropy_parameters
  obtain ⟨d₅, hd₅⟩ := eventually_linear_host_forest_error B M hM
  obtain ⟨d₆, hd₆⟩ := eventually_entropy_block_capacity (B + 3) C M
  refine ⟨d₁ + d₂ + d₃ + d₄ + d₅ + d₆, ?_⟩
  intro d hd n G hn hmin hmax hlocal hentropy
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hd₁' : d₁ ≤ d := by omega
  have hd₂' : d₂ ≤ d := by omega
  have hd₃' : d₃ ≤ d := by omega
  have hd₄' : d₄ ≤ d := by omega
  have hd₅' : d₅ ≤ d := by omega
  have hd₆' : d₆ ≤ d := by omega
  obtain ⟨hdlarge, hlog, hloglog, _, hdegreeScale, hdensityScale⟩ := hd₂ d hd₂'
  have hdpos : 0 < d := by omega
  have hdposR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hLpos : 0 < Real.log d := by linarith
  have hMpos : 0 < M := by linarith
  have hmin' : ∀ v, d ≤ G.degree v := by simpa only [G.ncard_neighborSet] using hmin
  have hmax' : ∀ v, G.degree v ≤ d ^ B := by simpa only [G.ncard_neighborSet] using hmax
  have hpositive : ∀ v, 0 < G.degree v := fun v => hdpos.trans_le (hmin' v)
  have hneighbors : ∀ v, ∃ w, G.Adj v w := fun v =>
    (G.degree_pos_iff_exists_adj v).mp (hpositive v)
  obtain ⟨w₀, hw₀⟩ := hneighbors ⟨0, hn⟩
  have hedge : ∃ u v, G.Adj u v := ⟨⟨0, hn⟩, w₀, hw₀⟩
  have he : (0 : ℝ) < G.edgeSet.ncard := by
    have h := (hpositive ⟨0, hn⟩).trans_le (G.degree_le_card_edgeFinset ⟨0, hn⟩)
    simpa only [G.edgeFinset_card, Set.fintypeCard_eq_ncard, Nat.cast_pos] using h
  by_contra hnot
  have hcheap : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * d) * G.edgeSet.ncard :=
    le_of_not_gt hnot
  obtain ⟨m, K, hKsize, hRamsey⟩ := sizeRamsey_attained G G
  have hKbudget : (K.edgeFinset.card : ℝ) ≤ (M * d) * G.edgeSet.ncard := by
    simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard, hKsize] using hcheap
  have hKpositive := ramsey_host_edges_positive G K hpositive hRamsey
  obtain ⟨J, hJK, hJdegree, hJdensity, hJcost⟩ := entropy_bounded_sparse_host G K B d M
    (by omega) hM (by linarith) hdegreeScale hdensityScale hmax' hcheap hKbudget
  obtain ⟨P, hP, hresidual⟩ := exists_dense_block_packing J (baselineBlockSize d) (1 / 4) (by norm_num)
  have hJdegree' : ∀ w, J.degree w ≤ d ^ (B + 3) := by
    simpa only [J.ncard_neighborSet] using hJdegree
  obtain ⟨t, hsupport, hgood⟩ := hd₃ d hd₃' (Fin m) n G hn hmin' hmax' hcheap
    J hJdegree' hJdensity P hP.boundedEdgeBlocks
  let E := repeatedBadSupport G J P (componentSize G t / 1024) t
  let H := J.deleteEdges (E : Set (Sym2 (Fin m)))
  have hHJ : H ≤ J := J.deleteEdges_le _
  have hHK : H ≤ K := hHJ.trans hJK
  let V := (componentRepresentative G t).supp
  let vertexEquiv := (Fintype.equivFin V).symm
  let F := (componentModel G t).comap vertexEquiv
  let e : F ≃g componentModel G t := SimpleGraph.Iso.comap vertexEquiv (componentModel G t)
  have hF : F.Connected := e.connected_iff.mpr (componentModel_connected G t)
  have hFG : F.IsContained G := (show F.IsContained (componentModel G t) from ⟨e.toCopy⟩).trans
    ⟨SimpleGraph.Copy.induce G (componentRepresentative G t).supp⟩
  have hFmin : ∀ v, d ≤ F.degree v := by
    intro v
    rw [← e.degree_eq v]
    simpa only [SimpleGraph.ncard_neighborSet] using
      (componentModel_degree_bounds G d (d ^ B) hmin' hmax' t (e v)).1
  have hpow : d ^ B ≤ d ^ (B + 3) := Nat.pow_le_pow_right hdpos (by omega)
  have hFmax : ∀ v, F.degree v ≤ d ^ (B + 3) := by
    intro v
    rw [← e.degree_eq v]
    have h := (componentModel_degree_bounds G d (d ^ B) hmin' hmax' t (e v)).2
    have hbound : (componentModel G t).degree (e v) ≤ d ^ B := by
      simpa only [SimpleGraph.ncard_neighborSet] using h
    exact hbound.trans hpow
  have hHdegree : ∀ w, H.degree w ≤ d ^ (B + 3) := fun w =>
    ((SimpleGraph.Copy.ofLE H J hHJ).degree_le w).trans (hJdegree' w)
  have hFcard : F.edgeFinset.card = componentSize G t := by
    rw [e.card_edgeFinset_eq]
    simp only [componentSize, SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have hrepeated : ∀ f : F.Copy H,
      repeatedEdgeVolume P (copyRawEdges f) < 3 * (F.edgeFinset.card / 1024) := by
    intro f
    rw [hFcard]
    simpa only [copyRawEdges_ofLE_comp, copyRawEdges_comp_iso] using hgood (f.comp e.symm.toCopy)
  have hnodense : ∀ S T : Finset (Fin m), S.card = baselineBlockSize d →
      T.card = baselineBlockSize d → Disjoint S T →
      (crossEdges (H.deleteEdges (blockEdgeUnion P : Set (Sym2 (Fin m)))) S T : ℝ) ≤
        (1 / 4 : ℝ) * baselineBlockSize d * baselineBlockSize d := by
    intro S T hS hT hST
    have hmono : (crossEdges (H.deleteEdges (blockEdgeUnion P : Set (Sym2 (Fin m)))) S T : ℝ) ≤
        crossEdges (J.deleteEdges (blockEdgeUnion P : Set (Sym2 (Fin m)))) S T := by
      exact_mod_cast crossEdges_mono (SimpleGraph.deleteEdges_mono hHJ) S T
    exact hmono.trans (hresidual S T hS hT hST)
  have hE : (E.card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / (16 * Real.log d) := by
    have hJedges : (J.edgeFinset.card : ℝ) ≤ K.edgeFinset.card := by
      exact_mod_cast Finset.card_le_card (SimpleGraph.edgeFinset_mono hJK)
    calc
      (E.card : ℝ) ≤ J.edgeFinset.card / (16 * M * d * Real.log d) := hsupport
      _ ≤ K.edgeFinset.card / (16 * M * d * Real.log d) :=
        div_le_div_of_nonneg_right hJedges (by positivity)
      _ ≤ ((M * d) * G.edgeSet.ncard) / (16 * M * d * Real.log d) :=
        div_le_div_of_nonneg_right hKbudget (by positivity)
      _ = (G.edgeSet.ncard : ℝ) / (16 * Real.log d) := by field_simp
  have hdeleted : ∀ g : G.Copy K,
      ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤
        (G.edgeSet.ncard : ℝ) / (4 * Real.log d) := by
    intro g
    have hcost : ((copyRawEdges g ∩ (K \ J).edgeFinset).card : ℝ) ≤
        (G.edgeSet.ncard : ℝ) / (8 * Real.log d) := by
      have heq : (K \ J).edgeSet.toFinite.toFinset = (K \ J).edgeFinset := by
        ext a
        simp only [Set.Finite.mem_toFinset, SimpleGraph.mem_edgeFinset]
      have h := hJcost g
      rw [heq] at h
      have hfrac : entropyAllowance d * G.edgeSet.ncard / 8 =
          (G.edgeSet.ncard : ℝ) / (8 * Real.log d) := by unfold entropyAllowance; ring
      exact h.trans_eq hfrac
    have hsum : ((copyRawEdges g ∩ (K \ H).edgeFinset).card : ℝ) ≤
        (copyRawEdges g ∩ (K \ J).edgeFinset).card + E.card := by
      exact_mod_cast copy_deleted_capacity_delete G K J E g
    have hnonneg : 0 ≤ (G.edgeSet.ncard : ℝ) / Real.log d := by positivity
    have h8 : (G.edgeSet.ncard : ℝ) / (8 * Real.log d) =
        ((G.edgeSet.ncard : ℝ) / Real.log d) / 8 := by ring
    have h16 : (G.edgeSet.ncard : ℝ) / (16 * Real.log d) =
        ((G.edgeSet.ncard : ℝ) / Real.log d) / 16 := by ring
    have h4 : (G.edgeSet.ncard : ℝ) / (4 * Real.log d) =
        ((G.edgeSet.ncard : ℝ) / Real.log d) / 4 := by ring
    rw [h8] at hcost
    rw [h16] at hE
    rw [h4]
    linarith
  obtain ⟨v⟩ := hF.nonempty
  have hdk : d ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using (hFmin v).trans (F.degree_lt_card_verts v).le
  have hdD : d ≤ d ^ (B + 3) := (hFmin v).trans (hFmax v)
  have haverage : d * Fintype.card V ≤ 2 * F.edgeFinset.card := by
    calc
      d * Fintype.card V = ∑ _ : Fin (Fintype.card V), d := by simp [mul_comm]
      _ ≤ ∑ v, F.degree v := Finset.sum_le_sum (fun v _ => hFmin v)
      _ = 2 * F.edgeFinset.card := F.sum_degrees_eq_twice_card_edges
  obtain ⟨_, hD, hdBlock, horder, hqD, havgBlock, hpB₀, hpB₁, hscale,
      hq, hsmall, hgap, hα₀, hα₁, hp₀, hp₁, hseed, hretention, hseedlog⟩ :=
    hd₁ d hd₁' (d ^ (B + 3)) hdD le_rfl (Fintype.card V) F.edgeFinset.card hdk haverage
  obtain ⟨_, _, _, _, hpHalf, hbase⟩ := hd₄ d hd₄'
  have herror : forestCountingError (Fintype.card (Fin n)) (Nat.card G.ConnectedComponent)
      K.edgeFinset.card (d ^ B) ≤ G.edgeSet.ncard := by
    have h := hd₅ d hd₅' n m G K hn hmin
      (by simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hKpositive)
      (by simpa only [K.edgeFinset_card, Set.fintypeCard_eq_ncard] using hKbudget)
    simpa only [Fintype.card_fin, K.edgeFinset_card, Set.fintypeCard_eq_ncard] using h
  let Ltotal := (G.edgeSet.ncard : ℝ) / (4 * Real.log d) + 2 * baselineBlockRate (B + 3) d *
    (2 * (C * Real.log d) * K.edgeFinset.card / ((1 / 4 : ℝ) * baselineBlockSize d) +
     2 * (C * Real.log d) * K.edgeFinset.card / ((1 / 4 : ℝ) * baselineBlockSize d))
  have hLtotal₀ : 0 ≤ Ltotal := by dsimp only [Ltotal]; positivity
  have hLtotal₁ : Ltotal ≤ (G.edgeSet.ncard : ℝ) / Real.log d :=
    entropy_total_capacity (B + 3) C M d G.edgeSet.ncard K.edgeFinset.card hC
      (by linarith) hdposR (by linarith) he.le hKbudget (hd₆ d hd₆')
  have hbudget := residual_entropy_log_budget d G.edgeSet.ncard (componentEntropyMass G)
    (forestCountingError (Fintype.card (Fin n)) (Nat.card G.ConnectedComponent) K.edgeFinset.card (d ^ B))
    Ltotal hdposR (by linarith) hloglog he (by linarith) hLtotal₀ hLtotal₁ herror hentropy
  have hQ : ValidBlockPacking K (baselineBlockSize d) (1 / 4) ∅ := by simp [ValidBlockPacking]
  obtain ⟨R, hRK, hred, hblue⟩ := finite_sparse_two_scale_entropy_coloring G F K H hHK hF hFG
    P ∅ (baselineBlockSize d) (baselineBlockSize d) (1 / 4) (1 / 4) (C * Real.log d)
    (hP.mono hJK) hQ (by simp [blockEdgeUnion]) hq (by omega) (by norm_num) (by norm_num) (by positivity)
    d (d ^ (B + 3)) (d ^ B) (baselineSeedOrder (B + 3) d (Fintype.card V))
    (F.edgeFinset.card / 256) (F.edgeFinset.card / 1024) (d / 512) (F.edgeFinset.card / 2)
    hdpos hFmin hFmax hHdegree hD hmax' hKpositive hneighbors hedge
    hdBlock horder hqD hqD havgBlock
    (baselineBlockRate (B + 3) d) (baselineSampleRate (B + 3) d) (baselineResidualRate d)
    hpB₀ hpB₁ hscale hα₀ hα₁ hp₀ hp₁
    (by simpa only [max_self] using hlocal) (by simpa only [Finset.union_empty] using hrepeated)
    hsmall hgap (by simpa only [Finset.union_empty] using hnodense) hseed hretention hseedlog
    ((G.edgeSet.ncard : ℝ) / (4 * Real.log d)) hdeleted hbase hbudget
  exact (hRamsey R hRK).elim hred hblue

end Erdos911
