import Erdos911.OrdinaryRoleEdges

namespace Erdos911

noncomputable def retentionDefects {V : Type*} [Fintype V]
    (G R : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel R.Adj] (ε : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (R.degree v : ℝ) < (1 - 2 * ε) * G.degree v)

theorem retentionDefects_degree_mass {V : Type*} [Fintype V] [DecidableEq V]
    (G R : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel R.Adj]
    (hR : R ≤ G) (ε : ℝ) :
    ε * (∑ v ∈ retentionDefects G R ε, (G.degree v : ℝ)) ≤ (G \ R).edgeFinset.card := by
  classical
  have hterm : ∀ v ∈ retentionDefects G R ε, 2 * ε * G.degree v ≤ ((G \ R).degree v : ℝ) := by
    intro v hv
    have hlow : (R.degree v : ℝ) < (1 - 2 * ε) * G.degree v := (Finset.mem_filter.mp hv).2
    have hpartition : ((G \ R).degree v : ℝ) + R.degree v = G.degree v := by
      exact_mod_cast subgraph_degree_partition G R hR v
    nlinarith only [hlow, hpartition]
  have hsum : 2 * ε * (∑ v ∈ retentionDefects G R ε, (G.degree v : ℝ)) ≤
      ∑ v, ((G \ R).degree v : ℝ) := by
    calc
      _ = ∑ v ∈ retentionDefects G R ε, 2 * ε * G.degree v := by rw [Finset.mul_sum]
      _ ≤ ∑ v ∈ retentionDefects G R ε, ((G \ R).degree v : ℝ) := Finset.sum_le_sum hterm
      _ ≤ ∑ v, ((G \ R).degree v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => Nat.cast_nonneg _)
  have htotal : (∑ v, ((G \ R).degree v : ℝ)) = 2 * (G \ R).edgeFinset.card := by
    have htotalNat : (∑ v, (G \ R).degree v) = 2 * (G \ R).edgeFinset.card := by
      simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using
        (G \ R).sum_degrees_eq_twice_card_edges
    exact_mod_cast htotalNat
  rw [htotal] at hsum
  linarith

theorem retentionDefects_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G R : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel R.Adj]
    (hR : R ≤ G) (d : ℕ) (hmin : ∀ v, d ≤ G.degree v) (ε : ℝ) (hε : 0 ≤ ε) :
    ε * d * (retentionDefects G R ε).card ≤ (G \ R).edgeFinset.card := by
  have hsum : (d : ℝ) * (retentionDefects G R ε).card ≤
      ∑ v ∈ retentionDefects G R ε, (G.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ retentionDefects G R ε, (d : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => by exact_mod_cast hmin v)
  have hscale := mul_le_mul_of_nonneg_left hsum hε
  have hmass := retentionDefects_degree_mass G R hR ε
  nlinarith only [hscale, hmass]

theorem retentionDefects_retained_degree {V : Type*} [Fintype V]
    (G R : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel R.Adj] (ε : ℝ) (v : V)
    (hv : v ∉ retentionDefects G R ε) : (1 - 2 * ε) * G.degree v ≤ (R.degree v : ℝ) := by
  classical
  apply le_of_not_gt
  intro h
  exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

end Erdos911
