import Erdos911.IncidenceCodegrees

namespace Erdos911

/-- In the strongly unbalanced class, heavy left pairs form a graph
of polynomial degree independent of the unbounded left scale P. -/
theorem heavy_incidence_degree_bound {L R : Type*} [DecidableEq L] [Fintype L]
    [DecidableEq R] [Fintype R] (N : R → Finset L) (d : ℕ) (P : ℝ)
    (hd : 1 ≤ d) (hP : 0 < P) (hrow : ∀ y, (N y).card ≤ d)
    (hcolumn : ∀ x, ((incidenceColumn N x).card : ℝ) ≤ (d : ℝ) ^ 4 * P) (x : L) :
    letI : DecidableRel (heavyIncidenceGraph N (P / (d : ℝ) ^ 12)).Adj := Classical.decRel _
    (heavyIncidenceGraph N (P / (d : ℝ) ^ 12)).degree x ≤ d ^ 17 := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let Q := heavyIncidenceGraph N (P / (d : ℝ) ^ 12)
  have hcharge := heavyIncidenceGraph_degree_charge N (P / (d : ℝ) ^ 12) d hrow x
  have hupper := mul_le_mul_of_nonneg_left (hcolumn x) hdR.le
  have hscaled := mul_le_mul_of_nonneg_left (hcharge.trans hupper) (pow_nonneg hdR.le 12)
  have hidentity : (d : ℝ) ^ 12 * (P / (d : ℝ) ^ 12 * Q.degree x) = P * Q.degree x := by
    field_simp
  rw [hidentity] at hscaled
  have hright : (d : ℝ) ^ 12 * ((d : ℝ) * ((d : ℝ) ^ 4 * P)) = P * (d : ℝ) ^ 17 := by ring
  rw [hright] at hscaled
  have h : (Q.degree x : ℝ) ≤ (d : ℝ) ^ 17 := by nlinarith only [hscaled, hP]
  exact_mod_cast h

noncomputable def closedNeighborFinset {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V := insert v (G.neighborFinset v)

theorem closedNeighborFinset_card {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedNeighborFinset G v).card = G.degree v + 1 := by
  simp [closedNeighborFinset, G.card_neighborFinset_eq_degree]

/-- A square-graph coloring partitions centers into classes with
pairwise disjoint closed neighborhoods. -/
theorem exists_disjoint_closed_neighborhood_coloring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) :
    ∃ c : V → Fin (D * (D + 1) + 1), ∀ u v, u ≠ v → c u = c v →
      Disjoint (closedNeighborFinset G u) (closedNeighborFinset G v) := by
  classical
  obtain ⟨c, hc⟩ := exists_degree_coloring (twoStepGraph G) (D * (D + 1))
    (twoStepGraph_degree_le G D hD)
  refine ⟨c, ?_⟩
  intro u v hne hcolor
  apply Finset.disjoint_left.mpr
  intro a hau hav
  have huv : (twoStepGraph G).Adj u v := by
    refine ⟨hne, ?_⟩
    rcases Finset.mem_insert.mp hau with hauEq | hau
    · rcases Finset.mem_insert.mp hav with h | hav
      · exact (hne (hauEq.symm.trans h)).elim
      · exact Or.inl (by simpa only [hauEq] using ((G.mem_neighborFinset v a).mp hav).symm)
    · rcases Finset.mem_insert.mp hav with havEq | hav
      · exact Or.inl (by simpa only [havEq] using (G.mem_neighborFinset u a).mp hau)
      · exact Or.inr ⟨a, (G.mem_neighborFinset u a).mp hau, ((G.mem_neighborFinset v a).mp hav).symm⟩
  exact hc u v huv hcolor

/-- A color class receives at least the reciprocal of the total number
of colors, measured by the number of assigned rows. -/
theorem exists_large_assignment_fiber {R A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
    (S : Finset R) (f : R → A) :
    ∃ a : A, S.card ≤ Fintype.card A * (S.filter (fun y => f y = a)).card := by
  classical
  let w := fun a : A => (S.filter (fun y => f y = a)).card
  have hsum : ∑ a : A, w a = S.card := by
    dsimp only [w]
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) w Finset.univ_nonempty
  have hbound : (∑ b : A, w b) ≤ Fintype.card A * w a := by
    calc
      _ ≤ ∑ _b : A, w a := Finset.sum_le_sum (fun b hb => ha b hb)
      _ = _ := by simp
  exact ⟨a, by simpa only [hsum] using hbound⟩

end Erdos911
