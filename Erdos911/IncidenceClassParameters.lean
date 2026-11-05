import Erdos911.IncidenceDegreeRatios
import Erdos911.NearRegularCopyCertificates

namespace Erdos911

/-- Every type in one order-and-edge-count class has the same two side
sizes. The left degree hypothesis gives the orientation entropy ratio. -/
theorem incidence_component_class_parameters {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (left right : Finset V)
    (hB : G.IsBipartiteWith (left : Set V) (right : Set V)) (d k e : ℕ) (τ : ℝ)
    (hd : 0 < d) (hlog : 1 ≤ Real.log d) (hτ : 0 ≤ τ)
    (hmin : ∀ v, d ≤ G.degree v) (hright : ∀ v ∈ right, G.degree v = d)
    (hleft : ∀ v ∈ left, (d : ℝ) * (Real.log d) ^ τ ≤ G.degree v)
    (hclass : (componentClass G k e).Nonempty) :
    ∃ a : ℕ, d ≤ k ∧ 0 < a ∧ a ≤ k ∧ 0 < e ∧
      (d : ℝ) * k ≤ 2 * e ∧ (e : ℝ) ≤ (d : ℝ) * k ∧
      τ * Real.log (Real.log d) ≤ Real.log ((k : ℝ) / a) ∧
      ∀ t ∈ componentClass G k e, (componentSide G t left).card = a ∧
        k ≤ 2 * (componentSide G t right).card := by
  classical
  have hneigh : ∀ v, ∃ w, G.Adj v w := by
    intro v
    have hp : 0 < (G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree]
      exact hd.trans_le (hmin v)
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hp
    exact ⟨w, (G.mem_neighborFinset v w).mp hw⟩
  obtain ⟨t₀, ht₀⟩ := hclass
  obtain ⟨horder, hedge⟩ := (mem_componentClass G k e t₀).mp ht₀
  let F := componentModel G t₀
  let L := componentSide G t₀ left
  let R := componentSide G t₀ right
  have hBF : F.IsBipartiteWith (L : Set _) (R : Set _) := componentSide_bipartite G left right hB t₀
  have hFmin : ∀ v, d ≤ F.degree v := fun v => by rw [componentModel_degree_eq]; exact hmin v.val
  have hFright : ∀ v ∈ R, F.degree v = d := by
    intro v hv
    rw [componentModel_degree_eq]
    exact hright v.val ((mem_componentSide G t₀ right v).mp hv)
  have hFleft : ∀ v ∈ L, (d : ℝ) * (Real.log d) ^ τ ≤ F.degree v := by
    intro v hv
    rw [componentModel_degree_eq]
    exact hleft v.val ((mem_componentSide G t₀ left v).mp hv)
  have hepos : 0 < e := by
    rw [← hedge]
    exact componentSize_pos G (fun v => (show 1 ≤ d by omega).trans (hmin v)) t₀
  have hpartition : L.card + R.card = k := by
    simpa only [horder] using componentSide_partition_card G left right hB hneigh t₀
  have hcard : Fintype.card (componentRepresentative G t₀).supp = k := by
    simpa only [componentOrder, Nat.card_eq_fintype_card] using horder
  have hdk : d ≤ k := by
    obtain ⟨v⟩ := (componentModel_connected G t₀).nonempty
    rw [← hcard]
    exact (hFmin v).trans (F.degree_lt_card_verts v).le
  have hsize : F.edgeSet.ncard = e := hedge
  have hbalance : e = d * R.card := by
    rw [← hedge]
    exact componentSide_right_edge_count G left right hB d hright t₀
  have hLpos : 0 < L.card := by
    by_contra hn
    have hEmpty : L = ∅ := Finset.card_eq_zero.mp (by omega)
    have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hBF
    rw [hEmpty, Finset.sum_empty, F.edgeFinset_card, Set.fintypeCard_eq_ncard, hsize] at hsum
    omega
  have hratio : (Real.log d) ^ τ * L.card ≤ (R.card : ℝ) :=
    bipartite_left_degree_ratio F L R hBF d hd _ hFright hFleft
  have hpow : 1 ≤ (Real.log d) ^ τ := Real.one_le_rpow hlog hτ
  obtain ⟨_, hhalf⟩ := incidence_bipartite_size_bounds k L.card R.card _ hpartition hpow hratio
  have haverage : (d : ℝ) * k ≤ 2 * e := by
    have h := (degree_edge_count_bounds F d F.maxDegree hFmin F.degree_le_maxDegree).1
    rw [hcard, hsize] at h
    linarith only [h]
  have hupper : (e : ℝ) ≤ (d : ℝ) * k := by
    rw [hbalance, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show R.card ≤ k by omega)) (Nat.cast_nonneg _)
  refine ⟨L.card, hdk, hLpos, by omega, hepos, haverage, hupper,
    incidence_orientation_log_ratio d τ k L.card R.card (by linarith) hLpos (by omega) hratio, ?_⟩
  intro t ht
  obtain ⟨horder', hedge'⟩ := (mem_componentClass G k e t).mp ht
  obtain ⟨hR, hL⟩ := componentSide_card_eq_of_class G left right hB hneigh d hd hright t t₀
    (horder'.trans horder.symm) (hedge'.trans hedge.symm)
  exact ⟨hL, by simpa only [hR] using hhalf⟩

end Erdos911
