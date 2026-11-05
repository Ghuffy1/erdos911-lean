import Erdos911.DegreePeeling
import Erdos911.ComponentModels
import Erdos911.CopyDensity

namespace Erdos911

/-- A weighted peeling argument gives a connected dense set directly.
No radius bound is needed when the palette controls all small connected sets. -/
theorem exists_weighted_dense_connected_set {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hvolume : (∑ v, w v) < 4 * R.edgeSet.ncard) :
    ∃ U : Finset V, U.Nonempty ∧ (R.induce (U : Set V)).Connected ∧
      (∑ v ∈ U, w v) ≤ 8 * (R.induce (U : Set V)).edgeSet.ncard := by
  classical
  obtain ⟨J, hJR, hdegree, hmass⟩ := exists_degree_peeling R (fun v => w v / 4)
    (fun v => div_nonneg (hw v) (by norm_num))
  have hcost : supportWeight R (fun v => w v / 4) ≤ (∑ v, w v) / 4 := by
    simpa only [Finset.sum_div] using supportWeight_le_sum R (fun v => w v / 4)
      (fun v => div_nonneg (hw v) (by norm_num))
  rw [R.edgeFinset_card, Set.fintypeCard_eq_ncard] at hmass
  have heJ : 0 < J.edgeSet.ncard := by
    have h : (0 : ℝ) < J.edgeSet.ncard := by linarith
    exact_mod_cast h
  obtain ⟨e, he⟩ := (Set.ncard_pos (s := J.edgeSet)).mp heJ
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : J.Adj u v := J.mem_edgeSet.mp he
    let c := J.connectedComponentMk u
    let U : Finset V := (Set.toFinite c.supp).toFinset
    have hUset : (U : Set V) = c.supp := by
      ext x
      simp only [U, Finset.mem_coe, Set.Finite.mem_toFinset]
    have hu : u ∈ c.supp := rfl
    have hUpos : U.Nonempty := ⟨u, by rw [← hUset] at hu; exact hu⟩
    have hsupport (x : c.supp) : x.val ∈ J.support := by
      by_cases hxu : x.val = u
      · exact hxu ▸ (show u ∈ J.support from ⟨v, huv⟩)
      · have hr := c.reachable_of_mem_supp x.property hu
        have hpos := hr.degree_pos_left hxu
        obtain ⟨y, hy⟩ := (J.degree_pos_iff_exists_adj x.val).mp hpos
        exact ⟨y, hy⟩
    let Jc := J.induce c.supp
    have hmin (x : c.supp) : w x.val / 4 ≤ (Jc.degree x : ℝ) := by
      have h := hdegree x.val (hsupport x)
      rw [← Jc.ncard_neighborSet, component_neighbor_ncard_eq]
      exact h
    have hsum : (∑ x : c.supp, w x.val) ≤ 8 * Jc.edgeSet.ncard := by
      have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset c.supp)) => hmin x)
      rw [← Finset.sum_div] at h
      have hdeg := Jc.sum_degrees_eq_twice_card_edges
      rw [Jc.edgeFinset_card, Set.fintypeCard_eq_ncard] at hdeg
      have hdegR : (∑ x : c.supp, (Jc.degree x : ℝ)) = 2 * Jc.edgeSet.ncard := by exact_mod_cast hdeg
      rw [hdegR] at h
      linarith
    let f : Jc.Copy (R.induce (U : Set V)) := {
      toHom := {
        toFun := fun x => ⟨x.val, by rw [hUset]; exact x.property⟩
        map_rel' := fun h => hJR h
      }
      injective' := by
        intro x y h
        exact Subtype.ext (congrArg (fun x : ↥(U : Set V) => x.val) h)
    }
    have hsurj : Function.Surjective f := by
      intro x
      refine ⟨⟨x.val, by rw [← hUset]; exact x.property⟩, ?_⟩
      exact Subtype.ext rfl
    have hconn := SimpleGraph.Connected.map f.toHom hsurj c.connected_toSimpleGraph
    have hcount : (Jc.edgeSet.ncard : ℝ) ≤ (R.induce (U : Set V)).edgeSet.ncard := by
      exact_mod_cast copy_edge_ncard_le f
    have hweight : (∑ x ∈ U, w x) = ∑ x : c.supp, w x.val := by
      rw [← Finset.sum_coe_sort U w]
      exact Fintype.sum_equiv (Set.equivOfEq hUset) _ _ (fun _ => rfl)
    exact ⟨U, hUpos, hconn, by rw [hweight]; linarith⟩

/-- A residual graph keeping at least three quarters of the target's edges
contains a connected set dense relative to the original target degrees. -/
theorem exists_relative_degree_dense_set {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj]
    (hRF : R ≤ F) (heF : 0 < F.edgeSet.ncard)
    (hkeep : (3 / 4 : ℝ) * F.edgeSet.ncard ≤ R.edgeSet.ncard) :
    ∃ U : Finset V, U.Nonempty ∧ (F.induce (U : Set V)).Connected ∧
      (∑ v ∈ U, (F.degree v : ℝ)) ≤ 8 * (R.induce (U : Set V)).edgeSet.ncard := by
  have hsum : (∑ v, (F.degree v : ℝ)) = 2 * F.edgeSet.ncard := by
    have h := F.sum_degrees_eq_twice_card_edges
    rw [F.edgeFinset_card, Set.fintypeCard_eq_ncard] at h
    exact_mod_cast h
  have he : (0 : ℝ) < F.edgeSet.ncard := by exact_mod_cast heF
  obtain ⟨U, hU, hconn, hweight⟩ := exists_weighted_dense_connected_set R
    (fun v => (F.degree v : ℝ)) (fun v => Nat.cast_nonneg _) (by rw [hsum]; linarith)
  exact ⟨U, hU, hconn.mono (fun _ _ h => hRF h), hweight⟩

theorem relative_degree_dense_set_order {V : Type*} [Fintype V] [DecidableEq V]
    (F R : SimpleGraph V) [DecidableRel F.Adj] [DecidableRel R.Adj]
    (d : ℕ) (hmin : ∀ v, d ≤ F.degree v) (U : Finset V) (hU : U.Nonempty)
    (hweight : (∑ v ∈ U, (F.degree v : ℝ)) ≤ 8 * (R.induce (U : Set V)).edgeSet.ncard) :
    (d : ℝ) / 4 ≤ U.card := by
  classical
  have hlow : (d : ℝ) * U.card ≤ ∑ v ∈ U, (F.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ U, (d : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ => by exact_mod_cast hmin v)
  let J := R.induce (U : Set V)
  have hupp : 2 * J.edgeSet.ncard ≤ U.card * U.card := by
    have hsum := J.sum_degrees_eq_twice_card_edges
    rw [J.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
    rw [← hsum]
    calc
      (∑ v, J.degree v) ≤ ∑ _v : ↥(U : Set V), U.card := Finset.sum_le_sum (fun v _ => by
        simpa [J] using (J.degree_lt_card_verts v).le)
      _ = U.card * U.card := by simp
  have huppR : (2 : ℝ) * J.edgeSet.ncard ≤ (U.card : ℝ) * U.card := by exact_mod_cast hupp
  have hpos : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.mpr hU
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  nlinarith only [hlow, hweight, huppR]

end Erdos911
