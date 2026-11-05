import Erdos911.IncidenceCrossCertificates
import Erdos911.OrientationPruning
import Erdos911.RestrictedStarAssignment
import Erdos911.MarkedNeighborhoodStars

namespace Erdos911

theorem sum_incident_claims_card_le_twice {I W : Type*}
    [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (index : I → W) (hinj : Function.Injective index) (R : I → Finset (Sym2 W))
    (S : Finset (Sym2 W)) (hR : ∀ i, R i ⊆ S)
    (hincident : ∀ i e, e ∈ R i → index i ∈ e) :
    (∑ i, ((R i).card : ℝ)) ≤ 2 * S.card := by
  classical
  have hpoint (e : Sym2 W) : (∑ i, if e ∈ R i then (1 : ℝ) else 0) ≤
      if e ∈ S then 2 else 0 := by
    by_cases he : e ∈ S
    · simp only [ite_eq_left he]
      have h := injective_incidence_overlap_two index hinj R hincident e
      simpa only [Finset.sum_boole] using (show
        (((Finset.univ : Finset I).filter (fun i => e ∈ R i)).card : ℝ) ≤ 2 by exact_mod_cast h)
    · have hnone : ∀ i, e ∉ R i := fun i hi => he (hR i hi)
      simp only [hnone, he, ite_false, Finset.sum_const_zero, le_refl]
  calc
    (∑ i, ((R i).card : ℝ)) = ∑ e : Sym2 W, ∑ i, if e ∈ R i then (1 : ℝ) else 0 := by
      simpa only [mul_one] using weighted_incidence_sum R (fun _ => 1)
    _ ≤ ∑ e : Sym2 W, if e ∈ S then (2 : ℝ) else 0 := Finset.sum_le_sum (fun e _ => hpoint e)
    _ = 2 * S.card := by
      rw [← Finset.sum_filter]
      simp [mul_comm]

noncomputable def copyLowNeighborEdges {V W : Type*} [Fintype V] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (v : V) : Finset (Sym2 W) :=
  ((F.neighborFinset v).filter (fun u => f u ∉ high)).image (fun u => s(f v, f u))

theorem copyLowNeighborEdges_card {V W : Type*} [Fintype V] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (v : V) :
    (copyLowNeighborEdges F f high v).card = ((F.neighborFinset v).filter (fun u => f u ∉ high)).card := by
  have hinj : Function.Injective (fun u : V => s(f v, f u)) := by
    intro u w h
    rcases Sym2.eq_iff.mp h with h | h
    · exact f.injective h.2
    · exact f.injective (h.2.trans h.1)
  exact Finset.card_image_of_injective _ hinj

theorem copy_high_low_neighbor_partition {V W : Type*} [Fintype V] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (v : V) :
    (copyHighNeighbors F f high v).card + (copyLowNeighborEdges F f high v).card = F.degree v := by
  classical
  rw [copyLowNeighborEdges_card]
  have hhigh : copyHighNeighbors F f high v =
      (F.neighborFinset v).filter (fun u => f u ∈ high) := by
    ext u
    simp only [mem_copyHighNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  rw [hhigh]
  simpa only [F.card_neighborFinset_eq_degree] using
    Finset.card_filter_add_card_filter_not (s := F.neighborFinset v) (fun u => f u ∈ high)

noncomputable def incidenceOrientationDefects {V W : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (right : Finset V) (high : Finset W) (d : ℕ) : Finset V :=
  right.filter (fun v => 2 * (copyHighNeighbors F f high v).card < d)

theorem incidenceOrientationDefects_large_complement {V W : Type*}
    [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (right : Finset V) (high : Finset W) (d : ℕ)
    (v : V) (hv : v ∈ right) (hvA : v ∉ incidenceOrientationDefects F f right high d) :
    (d : ℝ) / 2 ≤ (copyHighNeighbors F f high v).card := by
  have h : d ≤ 2 * (copyHighNeighbors F f high v).card := by
    apply Nat.le_of_not_gt
    intro h
    exact hvA (Finset.mem_filter.mpr ⟨hv, h⟩)
  have hR : (d : ℝ) ≤ 2 * (copyHighNeighbors F f high v).card := by exact_mod_cast h
  linarith

/-- A low-high orientation defect is charged to an edge at a low left
image. The factor four allows the two endpoint incidences of an edge. -/
theorem incidenceOrientationDefects_card_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (f : F.Copy H) (left right : Finset V) (high : Finset W) (d : ℕ)
    (hmin : ∀ v ∈ right, d ≤ F.degree v)
    (hneighbors : ∀ v ∈ right, ∀ u, F.Adj v u → u ∈ left) :
    (d : ℝ) * (incidenceOrientationDefects F f right high d).card ≤
      4 * ((copyRawEdges f ∩ incidentEdgesAtSet H
        ((left.filter (fun v => f v ∉ high)).image f)).card : ℝ) := by
  classical
  let A := incidenceOrientationDefects F f right high d
  let S := copyRawEdges f ∩ incidentEdgesAtSet H ((left.filter (fun v => f v ∉ high)).image f)
  let R := fun v : A => copyLowNeighborEdges F f high v.val
  have hR (v : A) : R v ⊆ S := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hFu, huLow⟩ := Finset.mem_filter.mp hu
    have hAdj := (F.mem_neighborFinset v.val u).mp hFu
    have hvright := (Finset.mem_filter.mp v.property).1
    apply Finset.mem_inter.mpr
    refine ⟨(mem_copyRawEdges_iff_exists f _).mpr ⟨⟨s(v.val, u), hAdj⟩, rfl⟩, ?_⟩
    apply (mem_incidentEdgesAtSet_iff H _ s(f v.val, f u)).mpr
    exact ⟨H.mem_edgeFinset.mpr (map_rel f.toHom hAdj), f u, Finset.mem_image.mpr
      ⟨u, Finset.mem_filter.mpr ⟨hneighbors v.val hvright u hAdj, huLow⟩, rfl⟩, by simp⟩
  have hinc (v : A) (e : Sym2 W) (he : e ∈ R v) : f v.val ∈ e := by
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp he
    simp
  have hsum := sum_incident_claims_card_le_twice (fun v : A => f v.val)
    (f.injective.comp Subtype.val_injective) R S hR hinc
  have hpoint (v : A) : (d : ℝ) ≤ 2 * (R v).card := by
    have hbad := (Finset.mem_filter.mp v.property).2
    have hdeg := hmin v.val (Finset.mem_filter.mp v.property).1
    have hsplit := copy_high_low_neighbor_partition F f high v.val
    have h : d ≤ 2 * (copyLowNeighborEdges F f high v.val).card := by omega
    exact_mod_cast h
  have hcount : (d : ℝ) * A.card ≤ 2 * (∑ v : A, ((R v).card : ℝ)) := by
    have h := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset A)) => hpoint v)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
      mul_comm, Finset.mul_sum] using h
  change (d : ℝ) * A.card ≤ 4 * S.card
  linarith only [hsum, hcount]

theorem orientation_pruned_copy_low_left_edges_lt {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T a : ℕ) (g : ℝ) (t : ComponentType G) (hsize : 0 < componentSize G t)
    (f : (componentModel G t).Copy
      (H.deleteEdges (orientationBadSupport G H K T a g t : Set (Sym2 W))))
    (left : Finset (componentRepresentative G t).supp) (ha : left.card ≤ a) :
    ((copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) ∩
      incidentEdgesAtSet H ((left.filter (fun v =>
        ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) v ∉ highHostVertices K T)).image
          ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f))).card : ℝ) < g := by
  classical
  apply lt_of_not_ge
  intro hmass
  have hbad := copy_mem_orientationPatterns (componentModel G t) H K
    ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) left T a g ha hmass
  exact orientationBadSupport_eliminates_bad_copies G H K T a g t hsize f hbad

theorem orientation_pruned_copy_defects_bound {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (T a d : ℕ) (g : ℝ) (t : ComponentType G) [DecidableRel (componentModel G t).Adj]
    (hsize : 0 < componentSize G t)
    (f : (componentModel G t).Copy
      (H.deleteEdges (orientationBadSupport G H K T a g t : Set (Sym2 W))))
    (left right : Finset (componentRepresentative G t).supp) (ha : left.card ≤ a)
    (hmin : ∀ v ∈ right, d ≤ (componentModel G t).degree v)
    (hneighbors : ∀ v ∈ right, ∀ u, (componentModel G t).Adj v u → u ∈ left) :
    (d : ℝ) * (incidenceOrientationDefects (componentModel G t)
      ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) right (highHostVertices K T) d).card <
        4 * g := by
  classical
  have hcount := incidenceOrientationDefects_card_bound (componentModel G t) H
    ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f) left right (highHostVertices K T) d
    hmin hneighbors
  have hmass := orientation_pruned_copy_low_left_edges_lt G H K T a g t hsize f left ha
  linarith only [hcount, hmass]

end Erdos911
