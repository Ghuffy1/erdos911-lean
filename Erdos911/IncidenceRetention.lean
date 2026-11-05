import Erdos911.IncidenceListAccuracy

namespace Erdos911

noncomputable def copyHighNeighborLoss {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (high : Finset W) (v : Fin n) : Finset (Fin n) :=
  (copyHighNeighbors F f high v).filter (fun u => ¬J.Adj (f v) (f u))

theorem copy_high_neighbor_partition {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (high : Finset W) (v : Fin n) :
    (candidateSlice (copyHighNeighbors F f high v)
      (fun j => J.neighborFinset (f j)) (f v)).card +
        (copyHighNeighborLoss F H J f high v).card = (copyHighNeighbors F f high v).card := by
  have heq : candidateSlice (copyHighNeighbors F f high v)
      (fun j => J.neighborFinset (f j)) (f v) =
      (copyHighNeighbors F f high v).filter (fun u => J.Adj (f v) (f u)) := by
    ext u
    simp only [candidateSlice, Finset.mem_filter, SimpleGraph.mem_neighborFinset, J.adj_comm]
  rw [heq]
  exact Finset.card_filter_add_card_filter_not (s := copyHighNeighbors F f high v) _

theorem copy_high_neighbor_loss_le {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (high : Finset W) (v : Fin n) :
    (copyHighNeighborLoss F H J f high v).card ≤ (F \ copyRetainedGraph J f).degree v := by
  apply Finset.card_le_card
  intro u hu
  obtain ⟨huU, huJ⟩ := Finset.mem_filter.mp hu
  have hFu := ((mem_copyHighNeighbors F f high v u).mp huU).1
  exact ((F \ copyRetainedGraph J f).mem_neighborFinset v u).mpr
    ⟨hFu, fun h => huJ h.2⟩

noncomputable def incidenceRetentionDefects {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d : ℕ) (ε : ℝ) : Finset (Fin n) :=
  right.filter (fun v => ε * d / 2 < (copyHighNeighborLoss F H J f high v).card)

theorem incidenceRetentionDefects_card_bound {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d : ℕ) (ε : ℝ) :
    ε * d * (incidenceRetentionDefects F H J f right high d ε).card ≤
      4 * ((F \ copyRetainedGraph J f).edgeFinset.card : ℝ) := by
  classical
  let E := incidenceRetentionDefects F H J f right high d ε
  have hpoint (v : Fin n) (hv : v ∈ E) :
      ε * d / 2 ≤ ((F \ copyRetainedGraph J f).degree v : ℝ) := by
    have hloss := (Finset.mem_filter.mp hv).2
    have hdegree : ((copyHighNeighborLoss F H J f high v).card : ℝ) ≤
        (F \ copyRetainedGraph J f).degree v := by exact_mod_cast copy_high_neighbor_loss_le F H J f high v
    exact hloss.le.trans hdegree
  have hsum : ε * d / 2 * E.card ≤ ∑ v, ((F \ copyRetainedGraph J f).degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ E, ε * d / 2 := by simp [mul_comm]
      _ ≤ ∑ v ∈ E, ((F \ copyRetainedGraph J f).degree v : ℝ) := Finset.sum_le_sum hpoint
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
  have htotal : (∑ v, ((F \ copyRetainedGraph J f).degree v : ℝ)) =
      2 * (F \ copyRetainedGraph J f).edgeFinset.card := by
    have h := (F \ copyRetainedGraph J f).sum_degrees_eq_twice_card_edges
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat, SimpleGraph.edgeFinset_card,
      Set.fintypeCard_eq_ncard] using congrArg (Nat.cast : ℕ → ℝ) h
  rw [htotal] at hsum
  dsimp only [E] at hsum
  linarith only [hsum]

theorem copy_low_of_high_neighbor {V W : Type*} [Fintype W]
    (F : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel K.Adj]
    (T : ℕ) (hH : H ≤ lowEndpointPrunedGraph K T) (f : F.Copy H)
    (v u : V) (hvu : F.Adj v u) (hu : f u ∈ highHostVertices K T) :
    f v ∉ highHostVertices K T := by
  have hu' := (mem_highHostVertices K T (f u)).mp hu
  have hlow := (hH (map_rel f.toHom hvu)).2
  change K.degree (f v) ≤ T ∨ K.degree (f u) ≤ T at hlow
  intro hv
  have hv' := (mem_highHostVertices K T (f v)).mp hv
  rcases hlow with hlow | hlow <;> omega

/-- Every tested role outside the explicit edge-loss exceptions has its
true image in the list. The exceptional set contains no untested left roles. -/
theorem incidence_true_image_outside_defects {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J K : SimpleGraph W)
    [DecidableRel J.Adj] [DecidableRel K.Adj]
    (T : ℕ) (hH : H ≤ lowEndpointPrunedGraph K T) (f : F.Copy H)
    (right : Finset (Fin n)) (d s : ℕ) (hd : 0 < d)
    (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (hτ : 0 < 1 - 4 * ε)
    (c : SeedDescription F H s) (hagree : seedMapAgrees F H s c f)
    (hacc : IncidenceSeedAccurate F H J f right (highHostVertices K T) d s p ε c)
    (v : Fin n)
    (hne : (incidenceCandidateList F H J right (highHostVertices K T) d s p (1 - 4 * ε) c v).Nonempty)
    (hvE : v ∉ incidenceRetentionDefects F H J f right (highHostVertices K T) d ε) :
    f v ∈ incidenceCandidateList F H J right (highHostVertices K T) d s p (1 - 4 * ε) c v := by
  obtain ⟨w, hw⟩ := hne
  have hlarge := incidence_tested_role_large F H J f right (highHostVertices K T) d s p ε
    (1 - 4 * ε) hp c hacc v w hw
  have hvright := ((mem_incidenceCandidateList F H J right (highHostVertices K T) d s p
    (1 - 4 * ε) c v w).mp hw).1
  have hloss : ((copyHighNeighborLoss F H J f (highHostVertices K T) v).card : ℝ) ≤ ε * d / 2 := by
    apply le_of_not_gt
    intro h
    exact hvE (Finset.mem_filter.mpr ⟨hvright, h⟩)
  obtain ⟨u, hvu, hu⟩ := incidence_candidate_actual_high_neighbor F H J right (highHostVertices K T)
    d s p (1 - 4 * ε) hτ c f hagree v w hw
  have hvLow := copy_low_of_high_neighbor F H K T hH f v u hvu hu
  apply incidence_true_image_mem_of_tested F H J f right (highHostVertices K T) d s p ε hp hε c hacc v
    ⟨w, hw⟩ hvLow
  have hU : (0 : ℝ) < (copyHighNeighbors F f (highHostVertices K T) v).card := by
    exact_mod_cast (show 0 < (copyHighNeighbors F f (highHostVertices K T) v).card by omega)
  have hquarter : (d : ℝ) ≤ 4 * (copyHighNeighbors F f (highHostVertices K T) v).card := by exact_mod_cast hlarge
  have hscaled := mul_le_mul_of_nonneg_left hquarter hε
  have hpartition :
      ((candidateSlice (copyHighNeighbors F f (highHostVertices K T) v)
        (fun j => J.neighborFinset (f j)) (f v)).card : ℝ) +
          (copyHighNeighborLoss F H J f (highHostVertices K T) v).card =
            (copyHighNeighbors F f (highHostVertices K T) v).card := by
    exact_mod_cast copy_high_neighbor_partition F H J f (highHostVertices K T) v
  apply (le_div_iff₀ hU).mpr
  nlinarith only [hpartition, hloss, hscaled]

end Erdos911
