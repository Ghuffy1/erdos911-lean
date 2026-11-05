import Erdos911.NearRegularPriorPruning
import Erdos911.NearRegularComponentColoring

namespace Erdos911

/-- A large triple-log component class gives an avoiding coloring of
every host in the specified near-regular degree and edge ranges. The
degree threshold is chosen before either finite vertex type. -/
theorem near_regular_class_coloring_ambient (A M C : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D Δ : ℕ) (G : SimpleGraph U) [DecidableRel G.Adj]
      (K H : SimpleGraph W) [DecidableRel K.Adj] [DecidableRel H.Adj],
    H ≤ K → (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ Δ) →
    (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
    d ≤ D → D ≤ d ^ 3 → (∀ w, H.degree w ≤ D) →
    16 * M * d * Δ ≤ (D : ℝ) → (D : ℝ) ≤ 32 * M * d * Δ →
    (K.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard →
    (∀ f : G.Copy K, ((copyRawEdges f ∩ (K \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4) →
    (∀ S : Finset U, S.card ≤ 2 * nearRegularBlockSize d →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
    (∃ k a : ℕ, Real.exp ((a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
      ((componentClass G k a).card : ℝ)) →
    ∃ R : SimpleGraph W, R ≤ K ∧ ¬G.IsContained R ∧ ¬G.IsContained (K \ R) := by
  classical
  obtain ⟨dP, hdP⟩ := near_regular_prior_pruning_ambient A M C hA hM hC
  obtain ⟨dC, hdC⟩ := near_regular_coloring_after_pruning_ambient_general A 1024 (by norm_num)
  refine ⟨max 2 (max dP dC), ?_⟩
  intro d hd U W _ _ _ _ D Δ G _ K H _ _ hHK hmin hmax hdegree hdD hDpow hhost hlower hupper
    hbudget hinitial hlocal hclass
  obtain ⟨k, a, hclass⟩ := hclass
  obtain ⟨J, hJ, hfirst, hsecond, t, _, P, hcapacity, hcopies⟩ := hdP d (by omega) U W D Δ G K H
    hHK hmin hmax hdegree hdD hDpow hhost hlower hupper hbudget hlocal k a hclass
  let F := componentModel G t
  let : DecidableRel J.Adj := Classical.decRel J.Adj
  have hF : F.Connected := componentModel_connected G t
  have hFG : F.IsContained G := ⟨SimpleGraph.Copy.induce G (componentRepresentative G t).supp⟩
  have hFmin : ∀ v, d ≤ F.degree v := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using (componentModel_degree_bounds G d Δ hmin hmax t v).1
  have hFmax : ∀ v, F.degree v ≤ Δ := by
    intro v
    simpa only [SimpleGraph.ncard_neighborSet] using (componentModel_degree_bounds G d Δ hmin hmax t v).2
  have hGpos : 0 < G.edgeSet.ncard := by
    have hsize := componentSize_pos G (fun v => (show 1 ≤ d by omega).trans (hmin v)) t
    exact hsize.trans_le (copy_edge_ncard_le (SimpleGraph.Copy.induce G (componentRepresentative G t).supp))
  have hΛ : (1 : ℝ) ≤ M * d := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have h := mul_nonneg (show 0 ≤ M by linarith) (sub_nonneg.mpr hd1)
    nlinarith only [h, hM]
  have hcutoff : 16 * (M * d) * Δ ≤ (D : ℝ) := by
    simpa only [mul_assoc] using hlower
  have hprior : ∀ f : G.Copy K, ((copyRawEdges f ∩ P).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 2 := by
    intro f
    have h := hcapacity f
    have hn : (0 : ℝ) ≤ G.edgeSet.ncard := Nat.cast_nonneg _
    linarith only [h, hn]
  exact hdC d (by omega) (componentRepresentative G t).supp U W D Δ F G K H J hF hFG hHK hJ
    hFmin hFmax hmax hdegree hDpow hhost hGpos hfirst hsecond (M * d) P hΛ hbudget hcutoff
    hinitial hprior (fun f hf => (hcopies f hf).1) (fun f hf => (hcopies f hf).2)

theorem near_regular_class_coloring (A M C : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M) (hC : 0 ≤ C) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (U W : Type*)
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W],
    ∀ (D Δ : ℕ) (G : SimpleGraph U) [DecidableRel G.Adj]
      (H : SimpleGraph W) [DecidableRel H.Adj],
    (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ Δ) →
    (Δ : ℝ) ≤ A * d * (Real.log d) ^ nearRegularDegreePower →
    d ≤ D → D ≤ d ^ 3 → (∀ w, H.degree w ≤ D) →
    16 * M * d * Δ ≤ (D : ℝ) → (D : ℝ) ≤ 32 * M * d * Δ →
    (H.edgeSet.ncard : ℝ) ≤ (M * d) * G.edgeSet.ncard →
    (∀ S : Finset U, S.card ≤ 2 * nearRegularBlockSize d →
      ((G.induce (S : Set U)).edgeSet.ncard : ℝ) ≤ C * Real.log d * S.card) →
    (∃ k a : ℕ, Real.exp ((a : ℝ) * (tripleLogEntropyThreshold d - 3 * Real.log 2)) ≤
      ((componentClass G k a).card : ℝ)) →
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  obtain ⟨d₀, hd₀⟩ := near_regular_class_coloring_ambient A M C hA hM hC
  refine ⟨d₀, ?_⟩
  intro d hd U W _ _ _ _ D Δ G _ H _ hmin hmax hdegree hdD hDpow hhost hlower hupper hbudget hlocal hclass
  have hinitial : ∀ f : G.Copy H,
      ((copyRawEdges f ∩ (H \ H).edgeFinset).card : ℝ) ≤ (G.edgeSet.ncard : ℝ) / 4 := by
    intro f
    have hself : (H \ H).edgeFinset = ∅ := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_sdiff, Set.mem_sdiff, Finset.notMem_empty]
      tauto
    rw [hself, Finset.inter_empty, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  exact hd₀ d hd U W D Δ G H H le_rfl hmin hmax hdegree hdD hDpow hhost hlower hupper hbudget
    hinitial hlocal hclass

end Erdos911
