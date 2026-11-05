import Erdos911.WeightedDegreeMedian
import Erdos911.DegreeCover

namespace Erdos911

/-- A cheap Ramsey target has maximum degree controlled by the
edge-weighted median on its high-degree side. The right-side bound is
used only to bound the maximum degree of the lower-median subtarget. -/
theorem exists_bipartite_median_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (r : ℕ) (Λ : ℝ)
    (he : 0 < G.edgeSet.ncard) (_hΛ : 0 ≤ Λ)
    (hleft : ∀ v ∈ left, v ∈ G.support → r ≤ G.degree v)
    (hright : ∀ v ∈ right, G.degree v ≤ r)
    (hRamsey : (SimpleGraph.sizeRamsey G G : ℝ) ≤ Λ * G.edgeSet.ncard) :
    ∃ p : ℕ, 0 < p ∧ r ≤ p ∧
      G.edgeSet.ncard ≤ 2 * (G.between ((left.filter (fun v => G.degree v ≤ p)) : Set V)
        (right : Set V)).edgeSet.ncard ∧
      G.edgeSet.ncard ≤ 2 * (G.between ((left.filter (fun v => p ≤ G.degree v)) : Set V)
        (right : Set V)).edgeSet.ncard ∧
      ∀ v, (G.degree v : ℝ) ≤ 4 * Λ * p := by
  classical
  obtain ⟨p, hp, ⟨v₀, hv₀, hdeg₀⟩, hlo, hhi⟩ := exists_bipartite_degree_median G left right hB he
  let : Nonempty V := ⟨v₀⟩
  have hrp : r ≤ p := by
    rw [← hdeg₀]
    apply hleft v₀ hv₀
    exact (G.degree_pos_iff_mem_support v₀).mp (by omega)
  let A := left.filter (fun v => G.degree v ≤ p)
  let F := G.between (A : Set V) (right : Set V)
  have hAG : A ⊆ left := Finset.filter_subset _ _
  have hFB : F.IsBipartiteWith (A : Set V) (right : Set V) := leftRestriction_bipartite G left right A hB hAG
  have hFG : F ≤ G := G.between_le
  have hFmax : F.maxDegree ≤ p := by
    apply F.maxDegree_le_of_forall_degree_le
    intro v
    by_cases hv : v ∈ F.support
    · obtain ⟨w, hvw⟩ := hv
      have hdeg : F.degree v ≤ G.degree v := (SimpleGraph.Copy.ofLE F G hFG).degree_le v
      rcases hFB.mem_of_adj hvw with h | h
      · exact hdeg.trans (Finset.mem_filter.mp h.1).2
      · exact hdeg.trans ((hright v h.1).trans hrp)
    · rw [(F.degree_eq_zero_iff_notMem_support v).mpr hv]
      exact Nat.zero_le _
  have hcover := degree_cover_size_bound G F ⟨SimpleGraph.Copy.ofLE F G hFG⟩
  rw [F.edgeFinset_card, Set.fintypeCard_eq_ncard] at hcover
  have hcoverR : (G.maxDegree : ℝ) * F.edgeSet.ncard ≤
      2 * (SimpleGraph.sizeRamsey G G : ℝ) * F.maxDegree := by exact_mod_cast hcover
  have heR : (0 : ℝ) < G.edgeSet.ncard := by exact_mod_cast he
  have hloN : G.edgeSet.ncard ≤ 2 * F.edgeSet.ncard := by
    simpa only [F, A, Finset.coe_filter] using hlo
  have hloR : (G.edgeSet.ncard : ℝ) ≤ 2 * F.edgeSet.ncard := by exact_mod_cast hloN
  have hFmaxR : (F.maxDegree : ℝ) ≤ p := by exact_mod_cast hFmax
  have hm₁ := mul_le_mul_of_nonneg_left hloR (Nat.cast_nonneg (α := ℝ) G.maxDegree)
  have hm₂ := mul_le_mul_of_nonneg_left hFmaxR
    (show 0 ≤ 2 * (SimpleGraph.sizeRamsey G G : ℝ) by positivity)
  have hm₃ := mul_le_mul_of_nonneg_right hRamsey (show 0 ≤ 2 * (p : ℝ) by positivity)
  have hmax : (G.maxDegree : ℝ) ≤ 4 * Λ * p := by nlinarith only [hm₁, hm₂, hm₃, hcoverR, heR]
  refine ⟨p, hp, hrp, hlo, hhi, ?_⟩
  intro v
  have hvR : (G.degree v : ℝ) ≤ G.maxDegree := by exact_mod_cast G.degree_le_maxDegree v
  exact hvR.trans hmax

end Erdos911
