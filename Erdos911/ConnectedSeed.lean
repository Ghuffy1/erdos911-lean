import Erdos911.SampledSeed
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace Erdos911

theorem reachable_of_adj_reachable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (h : ∀ u v, G.Adj u v → H.Reachable (f u) (f v))
    {u v : V} (huv : G.Reachable u v) : H.Reachable (f u) (f v) := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

def shortWalkGraph {V : Type*} (G : SimpleGraph V) (S : Finset V) : SimpleGraph S where
  Adj u v := u ≠ v ∧ ∃ p : G.Walk u.val v.val, p.length ≤ 3
  symm.symm _u _v h := ⟨h.1.symm, by
    obtain ⟨p, hp⟩ := h.2
    exact ⟨p.reverse, by simpa using hp⟩⟩
  loopless.irrefl _u h := h.1 rfl

theorem shortWalkGraph_reachable {V : Type*} (G : SimpleGraph V) (S : Finset V)
    {u v : S} (p : G.Walk u.val v.val) (hp : p.length ≤ 3) :
    (shortWalkGraph G S).Reachable u v := by
  by_cases huv : u = v
  · subst v
    exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (G := shortWalkGraph G S) ⟨huv, p, hp⟩

/-- A dominating set in a connected graph is connected using walks of length
at most three between its vertices. -/
theorem dominating_shortWalkGraph_connected {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (S : Finset V)
    (hdom : ∀ v, v ∈ S ∨ ∃ w ∈ S, G.Adj v w) :
    (shortWalkGraph G S).Connected := by
  classical
  have hclose : ∀ x : V, ∃ s : S, ∃ p : G.Walk x s.val, p.length ≤ 1 := by
    intro x
    rcases hdom x with hx | ⟨s, hs, hxs⟩
    · exact ⟨⟨x, hx⟩, .nil, by simp⟩
    · exact ⟨⟨s, hs⟩, hxs.toWalk, by simp⟩
  choose project paths hlength using hclose
  have hstep : ∀ u v, G.Adj u v →
      (shortWalkGraph G S).Reachable (project u) (project v) := by
    intro u v huv
    apply shortWalkGraph_reachable G S
      ((paths u).reverse.append (huv.toWalk.append (paths v)))
    simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Adj.length_toWalk]
    have hu := hlength u
    have hv := hlength v
    omega
  obtain ⟨x⟩ := hG.nonempty
  let : Nonempty S := ⟨project x⟩
  constructor
  intro u v
  have hu : (shortWalkGraph G S).Reachable u (project u.val) :=
    shortWalkGraph_reachable G S (paths u.val) ((hlength u.val).trans (by decide))
  have hv : (shortWalkGraph G S).Reachable v (project v.val) :=
    shortWalkGraph_reachable G S (paths v.val) ((hlength v.val).trans (by decide))
  exact hu.trans ((reachable_of_adj_reachable project hstep
    (hG u.val v.val)).trans hv.symm)

theorem short_walk_extra_card_le {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (u v : S) (huv : u ≠ v)
    (p : G.Walk u.val v.val) (hp : p.length ≤ 3) :
    (p.support.toFinset \ S).card ≤ 2 := by
  have hvalues : u.val ≠ v.val := fun h => huv (Subtype.ext h)
  have hpair : ({u.val, v.val} : Finset V) ⊆ p.support.toFinset ∩ S := by
    intro x hx
    have hx' : x = u.val ∨ x = v.val := by simpa using hx
    rcases hx' with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr p.start_mem_support, u.property⟩
    · exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr p.end_mem_support, v.property⟩
  have hinter : 2 ≤ (p.support.toFinset ∩ S).card := by
    simpa only [Finset.card_pair hvalues] using Finset.card_le_card hpair
  have hlength : p.support.toFinset.card ≤ 4 := by
    have h := List.toFinset_card_le p.support
    rw [p.length_support] at h
    omega
  have hsum := Finset.card_sdiff_add_card_inter p.support.toFinset S
  omega

/-- Connected patches along the edges of a connected auxiliary graph connect
all its vertex images and every vertex of the patches. -/
theorem connected_union_of_edge_patches {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (T : SimpleGraph S) [DecidableRel T.Adj]
    (hT : T.Connected) (C : T.edgeSet → Finset V)
    (hC : ∀ e, (G.induce (C e : Set V)).Connected)
    (hends : ∀ e : T.edgeSet, ∀ u : S, u ∈ e.val → u.val ∈ C e) :
    (G.induce ((S ∪ Finset.univ.biUnion C : Finset V) : Set V)).Connected := by
  classical
  let U := S ∪ Finset.univ.biUnion C
  have hSU : S ⊆ U := Finset.subset_union_left
  have hCU : ∀ e, C e ⊆ U := by
    intro e x hx
    exact Finset.mem_union_right S (Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hx⟩)
  let f : S → (U : Set V) := fun u => ⟨u.val, hSU u.property⟩
  have hstep : ∀ u v, T.Adj u v → (G.induce (U : Set V)).Reachable (f u) (f v) := by
    intro u v huv
    let e : T.edgeSet := ⟨s(u, v), huv⟩
    have hu : u.val ∈ C e := hends e u (by simp [e])
    have hv : v.val ∈ C e := hends e v (by simp [e])
    exact ((hC e) ⟨u.val, hu⟩ ⟨v.val, hv⟩).map
      (G.induceHomOfLE (show (C e : Set V) ⊆ (U : Set V) from hCU e)).toHom
  have hcore : ∀ u v : S, (G.induce (U : Set V)).Reachable (f u) (f v) :=
    fun u v => reachable_of_adj_reachable f hstep (hT u v)
  obtain ⟨root⟩ := hT.nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨f root, ?_⟩
  intro z
  rcases Finset.mem_union.mp z.property with hz | hz
  · exact hcore root ⟨z.val, hz⟩
  · obtain ⟨e, _, hzC⟩ := Finset.mem_biUnion.mp hz
    let u : S := e.val.out.1
    have huC : u.val ∈ C e := hends e u (Sym2.out_fst_mem e.val)
    have hpatch : (G.induce (U : Set V)).Reachable (f u) z :=
      ((hC e) ⟨u.val, huC⟩ ⟨z.val, hzC⟩).map
        (G.induceHomOfLE (show (C e : Set V) ⊆ (U : Set V) from hCU e)).toHom
    exact (hcore root u).trans hpatch

/-- Realize a spanning tree on the dominating vertices by short walks. Only
the internal vertices of those walks contribute to the enlargement. -/
theorem connected_superset_of_short_tree {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (T : SimpleGraph S) [DecidableRel T.Adj]
    (hT : T.IsTree) (hle : T ≤ shortWalkGraph G S) :
    ∃ U : Finset V, S ⊆ U ∧ (G.induce (U : Set V)).Connected ∧ U.card ≤ 3 * S.card := by
  classical
  have hadj : ∀ e : T.edgeSet, T.Adj e.val.out.1 e.val.out.2 := by
    intro e
    change s(e.val.out.1, e.val.out.2) ∈ T.edgeSet
    rw [show s(e.val.out.1, e.val.out.2) = e.val from e.val.out_eq]
    exact e.property
  have hshort : ∀ e : T.edgeSet,
      ∃ p : G.Walk e.val.out.1.val e.val.out.2.val, p.length ≤ 3 :=
    fun e => (hle (hadj e)).2
  choose paths hpaths using hshort
  let C : T.edgeSet → Finset V := fun e => (paths e).support.toFinset
  have hC : ∀ e, (G.induce (C e : Set V)).Connected := by
    intro e
    have hset : (C e : Set V) = {x | x ∈ (paths e).support} := by
      ext x
      exact List.mem_toFinset
    rw [hset]
    exact (paths e).connected_induce_support
  have hends : ∀ e : T.edgeSet, ∀ u : S, u ∈ e.val → u.val ∈ C e := by
    intro e u hu
    have heq : s(e.val.out.1, e.val.out.2) = e.val := e.val.out_eq
    have hu' : u ∈ s(e.val.out.1, e.val.out.2) := by rw [heq]; exact hu
    have heither : u = e.val.out.1 ∨ u = e.val.out.2 := by simpa using hu'
    rcases heither with rfl | rfl
    · exact List.mem_toFinset.mpr (paths e).start_mem_support
    · exact List.mem_toFinset.mpr (paths e).end_mem_support
  have hextra : ∀ e, (C e \ S).card ≤ 2 := by
    intro e
    exact short_walk_extra_card_le G S e.val.out.1 e.val.out.2
      (hle (hadj e)).1 (paths e) (hpaths e)
  let U := S ∪ Finset.univ.biUnion C
  have hU : U = S ∪ Finset.univ.biUnion (fun e => C e \ S) := by
    ext x
    by_cases hx : x ∈ S <;> simp [U, hx]
  refine ⟨U, Finset.subset_union_left, connected_union_of_edge_patches G S T hT.connected C hC hends,
    ?_⟩
  have htreecount : Fintype.card T.edgeSet + 1 = S.card := by
    simpa only [T.edgeFinset_card, Fintype.card_coe] using hT.card_edgeFinset
  rw [hU]
  calc
    (S ∪ Finset.univ.biUnion (fun e => C e \ S)).card ≤
        S.card + (Finset.univ.biUnion (fun e => C e \ S)).card := Finset.card_union_le _ _
    _ ≤ S.card + ∑ e : T.edgeSet, (C e \ S).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ S.card + ∑ _e : T.edgeSet, 2 :=
      Nat.add_le_add_left (Finset.sum_le_sum (fun e _ => hextra e)) _
    _ = S.card + Fintype.card T.edgeSet * 2 := by simp
    _ ≤ 3 * S.card := by omega

theorem exists_connected_dominating_superset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (S : Finset V)
    (hdom : ∀ v, v ∈ S ∨ ∃ w ∈ S, G.Adj v w) :
    ∃ U : Finset V, S ⊆ U ∧ (G.induce (U : Set V)).Connected ∧ U.card ≤ 3 * S.card := by
  classical
  obtain ⟨T, hle, hT⟩ := (dominating_shortWalkGraph_connected G hG S hdom).exists_isTree_le
  exact connected_superset_of_short_tree G S T hT hle

/-- Connect the sampled vertices and failed roles without changing the
sample. Every role outside the seed passes its tests and has a flagged neighbor. -/
theorem exists_connected_repair_seed {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.Connected)
    (p : Fin n → ℝ) (A : Fin n → Set (Fin n → Bool)) (ε : Fin n → ℝ)
    (hp₀ : ∀ j, 0 ≤ p j) (hp₁ : ∀ j, p j ≤ 1)
    (hA : ∀ v, cubeProbability p (A v) ≤ ε v)
    (hfailure : ∀ v ω, (∀ w ∈ G.neighborFinset v, ω w = false) → ω ∈ A v) :
    ∃ (ω : Fin n → Bool) (U : Finset (Fin n)),
      (∀ v, ω v = true → v ∈ U) ∧
        (∀ v ∉ U, ω ∉ A v) ∧
          (∀ v ∉ U, ∃ w ∈ U, G.Adj v w ∧ ω w = true) ∧
            (G.induce (U : Set (Fin n))).Connected ∧
              (U.card : ℝ) ≤ 3 * ((∑ j, p j) + ∑ v, ε v) := by
  classical
  obtain ⟨ω, S, hsample, hrepair, hdom, hsize⟩ :=
    exists_dominating_repair_set G p A ε hp₀ hp₁ hA hfailure
  obtain ⟨U, hSU, hconn, hcard⟩ := exists_connected_dominating_superset G hG S hdom
  have hpass : ∀ v ∉ U, ω ∉ A v := by
    intro v hv hbad
    exact hv (hSU (hrepair v hbad))
  refine ⟨ω, U, fun v hv => hSU (hsample v hv), hpass, ?_, hconn, ?_⟩
  · intro v hv
    have hex : ∃ w ∈ G.neighborFinset v, ω w = true := by
      by_contra hn
      apply hpass v hv
      apply hfailure v ω
      intro w hw
      cases he : ω w with
      | false => rfl
      | true => exact False.elim (hn ⟨w, hw, he⟩)
    obtain ⟨w, hw, htrue⟩ := hex
    exact ⟨w, hSU (hsample w htrue), (G.mem_neighborFinset v w).mp hw, htrue⟩
  · have hcardR : (U.card : ℝ) ≤ 3 * S.card := by exact_mod_cast hcard
    linarith

end Erdos911
