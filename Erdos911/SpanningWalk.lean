import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

namespace Erdos911

/-- Add one unvisited vertex by inserting a two-edge excursion at a visited
vertex. Connectedness supplies the boundary edge. -/
theorem extend_closed_walk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (root : V) (p : G.Walk root root)
    (hsmall : p.support.toFinset.card < Fintype.card V) :
    ∃ q : G.Walk root root,
      q.length = p.length + 2 ∧ q.support.toFinset.card = p.support.toFinset.card + 1 := by
  classical
  let S := p.support.toFinset
  have hnot : S ≠ Finset.univ := by
    intro h
    have hcard : S.card = Fintype.card V := by rw [h, Finset.card_univ]
    exact Nat.ne_of_lt hsmall hcard
  have hex : ∃ z, z ∉ S := by
    by_contra hn
    apply hnot
    ext z
    simp only [Finset.mem_univ, iff_true]
    by_contra hz
    exact hn ⟨z, hz⟩
  obtain ⟨z, hz⟩ := hex
  obtain ⟨path⟩ := hG root z
  obtain ⟨dart, _, hx, hy⟩ := path.exists_boundary_dart (S : Set V)
    (List.mem_toFinset.mpr p.start_mem_support) hz
  have hxlist : dart.fst ∈ p.support := List.mem_toFinset.mp hx
  obtain ⟨p₁, p₂, hp⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hxlist
  let q := p₁.append (dart.adj.toWalk.append (dart.adj.symm.toWalk.append p₂))
  have hlength : q.length = p.length + 2 := by
    simp only [q, SimpleGraph.Walk.length_append, SimpleGraph.Adj.length_toWalk]
    rw [hp, SimpleGraph.Walk.length_append]
    omega
  have hsupport : q.support.toFinset = insert dart.snd p.support.toFinset := by
    ext w
    have hxfst := p₁.end_mem_support
    simp only [q, hp, List.mem_toFinset, Finset.mem_insert,
      SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Adj.support_toWalk,
      List.mem_cons]
    aesop
  refine ⟨q, hlength, ?_⟩
  rw [hsupport, Finset.card_insert_of_notMem hy]

theorem exists_closed_walk_of_support_size {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (root : V) (k : ℕ)
    (hk : k < Fintype.card V) :
    ∃ p : G.Walk root root, p.length = 2 * k ∧ p.support.toFinset.card = k + 1 := by
  induction k with
  | zero => exact ⟨.nil, by simp, by simp [SimpleGraph.Walk.support]⟩
  | succ k ih =>
    obtain ⟨p, hlength, hcard⟩ := ih (by omega)
    have hsmall : p.support.toFinset.card < Fintype.card V := by omega
    obtain ⟨q, hlengthq, hcardq⟩ := extend_closed_walk G hG root p hsmall
    exact ⟨q, by omega, by omega⟩

/-- Every finite connected graph has a closed spanning walk of length
twice its order minus two, based at any prescribed vertex. -/
theorem exists_closed_spanning_walk {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (root : V) :
    ∃ p : G.Walk root root,
      p.length = 2 * (Fintype.card V - 1) ∧ p.support.toFinset = Finset.univ := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  obtain ⟨p, hlength, hcard⟩ := exists_closed_walk_of_support_size G hG root
    (Fintype.card V - 1) (by omega)
  refine ⟨p, hlength, Finset.eq_univ_of_card _ ?_⟩
  omega

end Erdos911
