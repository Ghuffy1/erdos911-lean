import Erdos911.IncidenceCrossRetention
import Erdos911.IncidenceCopyCertificates

namespace Erdos911

theorem incidence_retained_high_fraction {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 ≤ ε) (v : Fin n) (hv : v ∈ right)
    (hvE : v ∉ incidenceRetentionDefects F H J f right high d ε)
    (hquarter : d ≤ 4 * (copyHighNeighbors F f high v).card) :
    1 - 2 * ε ≤ ((candidateSlice (copyHighNeighbors F f high v)
      (fun j => J.neighborFinset (f j)) (f v)).card : ℝ) / (copyHighNeighbors F f high v).card := by
  have hU : (0 : ℝ) < (copyHighNeighbors F f high v).card := by
    exact_mod_cast (show 0 < (copyHighNeighbors F f high v).card by omega)
  have hloss : ((copyHighNeighborLoss F H J f high v).card : ℝ) ≤ ε * d / 2 := by
    apply le_of_not_gt
    intro h
    exact hvE (Finset.mem_filter.mpr ⟨hv, h⟩)
  have hquarterR : (d : ℝ) ≤ 4 * (copyHighNeighbors F f high v).card := by exact_mod_cast hquarter
  have hscaled := mul_le_mul_of_nonneg_left hquarterR hε
  have hpartition : ((candidateSlice (copyHighNeighbors F f high v)
      (fun j => J.neighborFinset (f j)) (f v)).card : ℝ) +
        (copyHighNeighborLoss F H J f high v).card = (copyHighNeighbors F f high v).card := by
    exact_mod_cast copy_high_neighbor_partition F H J f high v
  apply (le_div_iff₀ hU).mpr
  nlinarith only [hpartition, hloss, hscaled]

theorem incidence_large_role_true_image {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J K : SimpleGraph W)
    [DecidableRel J.Adj] [DecidableRel K.Adj] (T : ℕ)
    (hH : H ≤ lowEndpointPrunedGraph K T) (f : F.Copy H) (right : Finset (Fin n))
    (d s : ℕ) (hd : 0 < d) (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε)
    (c : SeedDescription F H s)
    (hacc : IncidenceSeedAccurate F H J f right (highHostVertices K T) d s p ε c)
    (v : Fin n) (hv : v ∈ right) (hvS : v ∉ c.1.val)
    (hvE : v ∉ incidenceRetentionDefects F H J f right (highHostVertices K T) d ε)
    (hlarge : (d : ℝ) / 2 ≤ (copyHighNeighbors F f (highHostVertices K T) v).card) :
    f v ∈ incidenceCandidateList F H J right (highHostVertices K T) d s p (1 - 4 * ε) c v := by
  have hquarter : d ≤ 4 * (copyHighNeighbors F f (highHostVertices K T) v).card := by
    have hU : (0 : ℝ) ≤ (copyHighNeighbors F f (highHostVertices K T) v).card := Nat.cast_nonneg _
    have h : (d : ℝ) ≤ 4 * (copyHighNeighbors F f (highHostVertices K T) v).card := by linarith
    exact_mod_cast h
  have hpos : 0 < (copyHighNeighbors F f (highHostVertices K T) v).card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  obtain ⟨hvu, huHigh⟩ := (mem_copyHighNeighbors F f (highHostVertices K T) v u).mp hu
  have hvLow := copy_low_of_high_neighbor F H K T hH f v u hvu huHigh
  exact incidence_true_image_mem F H J f right (highHostVertices K T) d s p ε hp hε c hacc v hv hvS
    hvLow hlarge (incidence_retained_high_fraction F H J f right (highHostVertices K T)
      d hd ε hε v hv hvE hquarter)

/-- The canonical matching loses only the orientation exceptions, the
connected seed, small-common-neighborhood roles, and removed cross edges. -/
theorem incidence_cross_matching_bound {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J K : SimpleGraph W)
    [DecidableRel J.Adj] [DecidableRel K.Adj] (T : ℕ)
    (hH : H ≤ lowEndpointPrunedGraph K T) (f : F.Copy H) (right A : Finset (Fin n))
    (B : Finset (Sym2 W)) (d s r : ℕ) (hd : 0 < d) (p ε R : ℝ)
    (hp : 0 < p) (hε : 0 < ε) (hτ : 0 < 1 - 4 * ε)
    (c : SeedDescription F H s) (hagree : seedMapAgrees F H s c f)
    (hacc : IncidenceSeedAccurate F H J f right (highHostVertices K T) d s p ε c)
    (hlarge : ∀ v ∈ right, v ∉ A →
      (d : ℝ) / 2 ≤ (copyHighNeighbors F f (highHostVertices K T) v).card)
    (hcross : ∀ x y, H.Adj x y → x ∉ highHostVertices K T → y ∈ highHostVertices K T →
      s(x, y) ∉ B → J.Adj x y) :
    (right.card : ℝ) ≤
      (matchedRoles (maximumListMatching (fun v : thickCandidateRoles J
        (incidenceCandidateList F H J right (highHostVertices K T) d s p (1 - 4 * ε) c) r R =>
          incidenceCandidateList F H J right (highHostVertices K T) d s p (1 - 4 * ε) c v.val))).card +
      (smallCommonNeighborhoodRoles J
        (incidenceCandidateList F H J right (highHostVertices K T) d s p (1 - 4 * ε) c) r R).card +
      A.card + s + 8 * ((copyRawEdges f ∩ B).card : ℝ) / (ε * d) := by
  classical
  let L := incidenceCandidateList F H J right (highHostVertices K T) d s p (1 - 4 * ε) c
  let E := incidenceRetentionDefects F H J f right (highHostVertices K T) d ε
  let A' := A ∪ c.1.val
  have hnonempty (v : Fin n) (hv : v ∈ right) (hvA : v ∉ A') (hvE : v ∉ E) : (L v).Nonempty := by
    obtain ⟨hvA, hvS⟩ := Finset.notMem_union.mp hvA
    exact ⟨f v, incidence_large_role_true_image F H J K T hH f right d s hd p ε hp hε.le
      c hacc v hv hvS hvE (hlarge v hv hvA)⟩
  have htrue (v : Fin n) (hne : (L v).Nonempty) (hvE : v ∉ E) : f v ∈ L v :=
    incidence_true_image_outside_defects F H J K T hH f right d s hd p ε hp hε.le hτ c hagree hacc v hne hvE
  have hm := incidence_matching_card_bound J L r R right A' E f f.injective hnonempty htrue
  have hmR : (right.card : ℝ) ≤ (matchedRoles (maximumListMatching
      (fun v : thickCandidateRoles J L r R => L v.val))).card +
      (smallCommonNeighborhoodRoles J L r R).card + A'.card + 2 * E.card := by exact_mod_cast hm
  have hA : (A'.card : ℝ) ≤ A.card + s := by
    have hcard : A'.card ≤ A.card + s :=
      (Finset.card_union_le A c.1.val).trans (Nat.add_le_add_left c.1.property.1 _)
    exact_mod_cast hcard
  have hE := incidenceRetentionDefects_cross_bound F H J K T hH f right B d ε hcross
  have hden : (0 : ℝ) < ε * d := mul_pos hε (by exact_mod_cast hd)
  have hE' : (E.card : ℝ) ≤ 4 * ((copyRawEdges f ∩ B).card : ℝ) / (ε * d) := by
    apply (le_div_iff₀ hden).mpr
    simpa only [E, mul_assoc, mul_comm, mul_left_comm] using hE
  have hEE : 2 * (E.card : ℝ) ≤ 8 * ((copyRawEdges f ∩ B).card : ℝ) / (ε * d) := by
    calc
      _ ≤ 2 * (4 * ((copyRawEdges f ∩ B).card : ℝ) / (ε * d)) :=
        mul_le_mul_of_nonneg_left hE' (by norm_num)
      _ = _ := by ring
  change (right.card : ℝ) ≤ (matchedRoles (maximumListMatching
      (fun v : thickCandidateRoles J L r R => L v.val))).card +
      (smallCommonNeighborhoodRoles J L r R).card + A.card + s +
        8 * ((copyRawEdges f ∩ B).card : ℝ) / (ε * d)
  linarith only [hmR, hA, hEE]

end Erdos911
