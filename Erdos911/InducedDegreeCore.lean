import Erdos911.DegreePeeling
import Erdos911.SupportTransfer

namespace Erdos911

/-- A set with more than s times its order edges contains a nonempty
induced subgraph of minimum degree at least s. -/
theorem exists_induced_degree_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Finset V) (s : ℕ)
    (hdense : (s : ℝ) * T.card < ((G.induce (T : Set V)).edgeSet.ncard : ℝ)) :
    ∃ U : Finset V, U ⊆ T ∧ U.Nonempty ∧
      ∀ v : ↥(U : Set V), s ≤ ((G.induce (U : Set V)).neighborSet v).ncard := by
  classical
  let F := G.induce (T : Set V)
  obtain ⟨S, H, hHF, hmin, hmass⟩ := exists_min_degree_subgraph F (s : ℝ) (by positivity)
  obtain ⟨f⟩ := hHF
  let g : H.Copy G := (SimpleGraph.Copy.induce G (T : Set V)).comp f
  let U : Finset V := Finset.univ.image g
  have hcard : U.card = Fintype.card S := Finset.card_image_of_injective _ g.injective
  have hsub : U ⊆ T := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact (f w).property
  have heH : 0 < H.edgeSet.ncard := by
    rw [F.edgeFinset_card, Set.fintypeCard_eq_ncard] at hmass
    have hcardT : Fintype.card ↥(T : Set V) = T.card := Fintype.card_coe T
    rw [hcardT] at hmass
    have h : (0 : ℝ) < H.edgeSet.ncard := by linarith
    exact_mod_cast h
  have hnonempty : Nonempty S := by
    obtain ⟨e, he⟩ := (Set.ncard_pos (s := H.edgeSet)).mp heH
    induction e using Sym2.inductionOn with
    | _ u v => exact ⟨u⟩
  let : Nonempty S := hnonempty
  have hUne : U.Nonempty := Finset.univ_nonempty.image g
  let fU : H.Copy (G.induce (U : Set V)) := {
    toHom := {
      toFun := fun w => ⟨g w, Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩⟩
      map_rel' := fun h => map_rel g.toHom h
    }
    injective' := by
      intro a b h
      have heq : g a = g b := congrArg (fun v : ↥(U : Set V) => v.val) h
      exact g.injective heq
  }
  refine ⟨U, hsub, hUne, ?_⟩
  intro v
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp v.property
  have heq : fU w = v := Subtype.ext hw
  have hminw : s ≤ H.degree w := by
    exact_mod_cast (show (s : ℝ) ≤ H.degree w by simpa only [H.ncard_neighborSet] using hmin w)
  have h := hminw.trans (fU.degree_le w)
  rw [heq] at h
  simpa only [SimpleGraph.ncard_neighborSet] using h

end Erdos911
