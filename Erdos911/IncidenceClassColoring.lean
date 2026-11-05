import Erdos911.IncidencePriorPruning

namespace Erdos911

/-- An unequal exact-right-degree target with a large component class
has an avoiding coloring in every host satisfying the initial bounds. -/
theorem incidence_class_coloring (A : ℕ) (M C τ : ℝ)
    (hM : 1 ≤ M) (hC : 0 ≤ C) (hτ : 0 < τ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D P : ℕ) (G : SimpleGraph U) [DecidableRel G.Adj]
      (K H : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj],
    H ≤ lowEndpointPrunedGraph K P → (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ D) →
    d ≤ D → D ≤ d ^ A → (∀ w, H.degree w ≤ D) →
    32 * M * (d : ℝ) ^ 2 ≤ (P : ℝ) → (P : ℝ) ≤ 64 * M * (d : ℝ) ^ 2 →
    (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard →
    (∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4) →
    (∀ S : Finset U, S.card ≤ 2 * nearRegularBlockSize d →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
    ∀ left right : Finset U, G.IsBipartiteWith (left : Set U) (right : Set U) →
    (∀ v ∈ right, G.degree v = d) →
    (∀ v ∈ left, (d : ℝ) * (Real.log d) ^ τ ≤ G.degree v) →
    (∃ k e : ℕ, Real.exp ((e : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
      ((componentClass G k e).card : ℝ)) →
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  obtain ⟨dP, hdP⟩ := incidence_prior_pruning A M C τ hM hC hτ
  obtain ⟨dC, hdC⟩ := incidence_coloring_after_pruning_general A 1024 (by norm_num)
  obtain ⟨dL, hdL⟩ := eventually_baseline_residual_bounds A
  refine ⟨max 2 (max dP (max dC dL)), ?_⟩
  intro d hd U W _ _ _ _ D P G _ K H _ _ hH hmin hmax hdD hDpow hhost hlower hupper
    hbudget hinitial hlocal left right hBip hright hleft hclass
  have hdpos : 0 < d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hPd : d ≤ P := by
    have hM' : (1 : ℝ) ≤ 32 * M := by linarith only [hM]
    have hs := mul_le_mul_of_nonneg_right hM' (sq_nonneg (d : ℝ))
    have hdSq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hdR]
    have h : (d : ℝ) ≤ P := by nlinarith only [hs, hdSq, hlower]
    exact_mod_cast h
  obtain ⟨k, e, hclass⟩ := hclass
  obtain ⟨J, hJ, hfirst, hsecond, t, ht, prior, removed, hcross, hcapacity, hcopies⟩ :=
    hdP d (by omega) U W D P G K H hH hmin hdD hDpow hhost hlower hupper hbudget hlocal
      left right hBip hright hleft k e hclass
  let : DecidableRel J.Adj := Classical.decRel J.Adj
  let F := componentModel G t
  have hFG : F.IsContained G := ⟨SimpleGraph.Copy.induce G (componentRepresentative G t).supp⟩
  have hFmin : ∀ v, d ≤ F.degree v := fun v => by rw [componentModel_degree_eq]; exact hmin v.val
  have hFmax : ∀ v, F.degree v ≤ D := fun v => by rw [componentModel_degree_eq]; exact hmax v.val
  have hFright : ∀ v ∈ componentSide G t right, F.degree v ≤ d := by
    intro v hv
    rw [componentModel_degree_eq, hright v.val ((mem_componentSide G t right v).mp hv)]
  have hbalance : F.edgeSet.ncard = d * (componentSide G t right).card :=
    componentSide_right_edge_count G left right hBip d hright t
  have hclasspos : (componentClass G k e).Nonempty := ⟨t, ht⟩
  obtain ⟨_, _, _, _, _, _, _, _, hside⟩ := incidence_component_class_parameters G left right hBip
    d k e τ hdpos (by have h := (hdL d (by omega)).2.1; linarith only [h]) hτ.le hmin hright hleft hclasspos
  have hcard : Fintype.card (componentRepresentative G t).supp = k := by
    have ho := ((mem_componentClass G k e t).mp ht).1
    simpa only [componentOrder, Nat.card_eq_fintype_card] using ho
  have hhalf : Fintype.card (componentRepresentative G t).supp ≤ 2 * (componentSide G t right).card := by
    rw [hcard]
    exact (hside t ht).2
  have hGpos : 0 < G.edgeSet.ncard := by
    have hs := componentSize_pos G (fun v => (show 1 ≤ d by omega).trans (hmin v)) t
    exact hs.trans_le (copy_edge_ncard_le (SimpleGraph.Copy.induce G (componentRepresentative G t).supp))
  have hΛ : (1 : ℝ) ≤ M * d := by
    have h := mul_nonneg (show 0 ≤ M by linarith) (sub_nonneg.mpr hdR)
    nlinarith only [h, hM]
  have hprior : ∀ f : G.Copy K, ((copyRawEdges f ∩ prior).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 2 := by
    intro f
    have h := hcapacity f
    have hn : (0 : ℝ) ≤ G.edgeSet.ncard := Nat.cast_nonneg _
    linarith only [h, hn]
  have hcover : G.IsVertexCover (right : Set U) := bipartite_right_isVertexCover G left right hBip
  exact hdC d (by omega) (componentRepresentative G t).supp U W D P hPd F G K H J
    (componentModel_connected G t) hFG hH hJ hFmin hFmax hDpow hhost hGpos
    (componentSide G t right) right hFright hbalance hhalf hcover (fun v hv => (hright v hv).le)
    hfirst hsecond (M * d) prior removed hΛ hbudget (by nlinarith only [hlower]) hcross hinitial hprior
    (fun f hf => (hcopies f hf).1) (fun f hf => (hcopies f hf).2.1) (fun f hf => (hcopies f hf).2.2)

end Erdos911
