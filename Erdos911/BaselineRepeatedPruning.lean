import Erdos911.BaselineTypeLogBounds
import Erdos911.RepeatedSupportSelection

namespace Erdos911

/-- A cheap polynomial-degree target supplies a component type whose
repeated-block bad-copy support is small. All counting parameters follow
from the target and host hypotheses. -/
theorem baseline_repeated_type_pruning (B : ℕ) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W : Type*) [Fintype W] [DecidableEq W],
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      0 < n → (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ d ^ B) →
      (SimpleGraph.sizeRamsey G G : ℝ) ≤ baselineHostMultiplier d * G.edgeSet.ncard →
      ∀ (J : SimpleGraph W) [DecidableRel J.Adj],
      (∀ w, J.degree w ≤ d ^ (B + 3)) →
      (∀ S : Finset W, (J.induce (S : Set W)).edgeSet.ncard ≤ baselineDensityCutoff B d * S.card) →
      ∀ P : Finset (RectangleBlock W),
      BoundedEdgeBlocks P (baselineBlockSize d * baselineBlockSize d) →
      ∃ t : ComponentType G,
        ((repeatedBadSupport G J P (componentSize G t / 1024) t).card : ℝ) ≤
          J.edgeFinset.card / (16 * baselineHostMultiplier d) ∧
        ∀ f : (componentModel G t).Copy
            (J.deleteEdges (repeatedBadSupport G J P (componentSize G t / 1024) t : Set (Sym2 W))),
          repeatedEdgeVolume P (copyRawEdges
            ((SimpleGraph.Copy.ofLE _ J (J.deleteEdges_le _)).comp f)) < 3 * (componentSize G t / 1024) := by
  obtain ⟨d₁, hd₁⟩ := polynomial_counterexample_class_lower 2 B
  obtain ⟨d₂, hd₂⟩ := eventually_baseline_host_parameters
  obtain ⟨d₃, hd₃⟩ := eventually_baseline_type_log_bounds B
  refine ⟨max d₁ (max d₂ (max d₃ (32768 * (B + 3)))), ?_⟩
  intro d hd W _ _ n G _ hn hmin hmax hcheap J _ hJdegree hJdensity P hP
  classical
  have hd₁' : d₁ ≤ d := (le_max_left _ _).trans hd
  have hrest : max d₂ (max d₃ (32768 * (B + 3))) ≤ d := (le_max_right _ _).trans hd
  have hd₂' : d₂ ≤ d := (le_max_left _ _).trans hrest
  have hrest' : max d₃ (32768 * (B + 3)) ≤ d := (le_max_right _ _).trans hrest
  have hd₃' : d₃ ≤ d := (le_max_left _ _).trans hrest'
  have hscale : 32768 * (B + 3) ≤ d := (le_max_right _ _).trans hrest'
  obtain ⟨hdlarge, hlog, hloglog, hΛ₀, hΛ₁⟩ := hd₂ d hd₂'
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hΛpower : baselineHostMultiplier d ≤ (d : ℝ) ^ 2 := hΛ₁.trans (by nlinarith)
  have hcheap' : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (d : ℝ) ^ 2 * G.edgeSet.ncard :=
    hcheap.trans (mul_le_mul_of_nonneg_right hΛpower (Nat.cast_nonneg _))
  obtain ⟨t₀, hclass⟩ := hd₁ d hd₁' n G hn
    (by simpa only [G.ncard_neighborSet] using hmin)
    (by simpa only [G.ncard_neighborSet] using hmax) hcheap'
  let k := componentOrder G t₀
  let a := componentSize G t₀
  have hk : 0 < k := componentOrder_pos G t₀
  have haverage : d * k ≤ 2 * a := component_degree_sum_bound G d hmin t₀
  have hdk : d ≤ d * k := by
    calc
      d = d * 1 := by omega
      _ ≤ d * k := Nat.mul_le_mul_left d (by omega)
  have ha : 65536 ≤ a := by omega
  have hFG : (componentModel G t₀).IsContained G :=
    ⟨SimpleGraph.Copy.induce G (componentRepresentative G t₀).supp⟩
  have hdensity : (a : ℝ) ≤ baselineTargetDensity B d * k := by
    have h := baseline_subgraph_density_bound (componentModel G t₀) G hFG B d
      (by omega) (by linarith) hΛ₀ hmax hcheap
    simpa only [a, k, componentSize, componentOrder, Nat.card_eq_fintype_card] using h
  have hratios := hd₃ d hd₃' k a (by omega) haverage hdensity
  have hM : ∀ S : Finset W, S.card = k →
      (J.induce (S : Set W)).edgeSet.ncard ≤ baselineDensityCutoff B d * k := by
    intro S hS
    simpa only [hS] using hJdensity S
  have hΛpos : 0 < baselineHostMultiplier d := by linarith
  have hTpos : 0 < baselineDensityCutoff B d := by
    have hσpos : 0 < baselineTargetDensity B d := by unfold baselineTargetDensity; positivity
    have h := Nat.le_ceil (32 * baselineHostMultiplier d * baselineTargetDensity B d)
    have hreal : (0 : ℝ) < baselineDensityCutoff B d :=
      (show 0 < 32 * baselineHostMultiplier d * baselineTargetDensity B d by positivity).trans_le h
    exact_mod_cast hreal
  have hqpos : 0 < baselineBlockSize d := by
    have h := Nat.le_ceil ((Real.log d) ^ 4)
    have hreal : (0 : ℝ) < baselineBlockSize d := (pow_pos (by linarith : 0 < Real.log d) 4).trans_le h
    exact_mod_cast hreal
  have hclass' : Real.exp ((1 - 1 / 32768 : ℝ) * a * Real.log d) ≤
      ((componentClass G k a).card : ℝ) := hclass.le
  obtain ⟨t, ht, hsupport, hgood⟩ := exists_repeated_type_with_small_support G J P
    (baselineBlockSize d * baselineBlockSize d) hP (B + 3) d k a (d ^ (B + 3))
    (baselineDensityCutoff B d * k) (baselineHostMultiplier d) hscale hlog ha haverage hJdegree
    (Nat.one_le_pow _ _ (by omega)) le_rfl hM (Nat.mul_pos hTpos hk) (Nat.mul_pos hqpos hqpos)
    hΛpos hΛ₁ hratios.1 hratios.2 hclass'
  have hsize : componentSize G t = a := (mem_componentClass G k a t).mp ht |>.2
  refine ⟨t, ?_, ?_⟩
  · rw [hsize]
    exact hsupport
  · rw [hsize]
    exact hgood

end Erdos911
