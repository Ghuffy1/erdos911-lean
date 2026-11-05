import Erdos911.DictionaryScales
import Erdos911.ConnectedLabelWeights

namespace Erdos911

noncomputable def dictionaryRowSupport {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V) :
    Finset ↥(dictionaryLowVertices K (dictionaryLowDegree q)) := by
  classical
  exact W.biUnion (incidenceColumn (dictionaryHostRows K (dictionaryLowDegree q)))

theorem mem_dictionaryRowSupport {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V)
    (y : ↥(dictionaryLowVertices K (dictionaryLowDegree q))) :
    y ∈ dictionaryRowSupport K q W ↔ ∃ x ∈ W, K.Adj x y.val := by
  classical
  constructor
  · intro hy
    obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp hy
    exact ⟨x, hx, ((mem_restrictedHostRows K _ _ y x).mp (Finset.mem_filter.mp hyx).2).2⟩
  · rintro ⟨x, hx, hxy⟩
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (mem_restrictedHostRows K _ _ y x).mpr ⟨Finset.mem_univ _, hxy⟩⟩⟩

theorem dictionaryRowSupport_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (W : Finset V) (j : ℕ)
    (hW : W.card ≤ dictionaryLeftSize q) (hj : AdmissibleDictionaryScale K q W j) :
    (dictionaryRowSupport K q W).card ≤ 2 * dictionaryLeftSize q * dictionaryDegreeCharge q * 2 ^ j := by
  classical
  calc
    (dictionaryRowSupport K q W).card ≤
        ∑ x ∈ W, (incidenceColumn (dictionaryHostRows K (dictionaryLowDegree q)) x).card := Finset.card_biUnion_le
    _ ≤ ∑ x ∈ W, K.degree x := Finset.sum_le_sum (fun x _ => dictionaryHostRows_column_le K _ x)
    _ ≤ ∑ _x ∈ W, 2 * dictionaryDegreeCharge q * 2 ^ j :=
      Finset.sum_le_sum (fun x hx => (hj.2.2 x hx).le)
    _ = W.card * (2 * dictionaryDegreeCharge q * 2 ^ j) := by simp
    _ ≤ dictionaryLeftSize q * (2 * dictionaryDegreeCharge q * 2 ^ j) := Nat.mul_le_mul_right _ hW
    _ = _ := by ring

/-- A low host row belongs to only boundedly many small connected
left supports, by rooting each support at one of the row's neighbors. -/
theorem dictionaryRowSupport_incidence_le {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (q : ℕ) (hq : 0 < q)
    (y : ↥(dictionaryLowVertices K (dictionaryLowDegree q))) :
    ((smallConnectedSets (concreteDictionaryGraph K q) (dictionaryLeftSize q)).filter
      (fun W => y ∈ dictionaryRowSupport K q W)).card ≤
      dictionaryLowDegree q * ((dictionaryLeftSize q + 1) * dictionaryConflictDegree q ^ (2 * dictionaryLeftSize q)) := by
  classical
  let Q := concreteDictionaryGraph K q
  let a := dictionaryLeftSize q
  let R := dictionaryConflictDegree q
  have hR : 1 ≤ R := by
    have hp : 0 < R := by
      dsimp only [R, dictionaryConflictDegree, dictionaryLowDegree, dictionaryDegreeCharge,
        dictionaryPatternCount, dictionaryLeftSize]
      positivity
    omega
  have hsub : ((smallConnectedSets Q a).filter (fun W => y ∈ dictionaryRowSupport K q W)) ⊆
      (K.neighborFinset y.val).biUnion (fun x => rootedConnectedSetsAtMost Q x a) := by
    intro W hW
    obtain ⟨hW', hy⟩ := Finset.mem_filter.mp hW
    obtain ⟨_, hsize, hconn⟩ := (mem_smallConnectedSets Q a W).mp hW'
    obtain ⟨x, hx, hxy⟩ := (mem_dictionaryRowSupport K q W y).mp hy
    exact Finset.mem_biUnion.mpr ⟨x, (K.mem_neighborFinset y.val x).mpr hxy.symm,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hsize, hconn⟩⟩
  calc
    _ ≤ ((K.neighborFinset y.val).biUnion (fun x => rootedConnectedSetsAtMost Q x a)).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ K.neighborFinset y.val, (rootedConnectedSetsAtMost Q x a).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ K.neighborFinset y.val, (a + 1) * R ^ (2 * a) :=
      Finset.sum_le_sum (fun x _ => rooted_connected_sets_at_most_count Q R
        (concreteDictionaryGraph_degree_le K q) hR x a)
    _ = K.degree y.val * ((a + 1) * R ^ (2 * a)) := by simp
    _ ≤ dictionaryLowDegree q * ((a + 1) * R ^ (2 * a)) :=
      Nat.mul_le_mul_right _ (Finset.mem_filter.mp y.property).2

end Erdos911
