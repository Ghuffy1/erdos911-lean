import Erdos911.SizeRamsey
import Mathlib.Combinatorics.SimpleGraph.Clique
import Lean.Elab.Tactic.Omega

/-!
Elementary finite two-color Ramsey existence. This supplies nonemptiness of
the set in the exact `sizeRamsey` definition, independently of the manuscript.
-/

namespace Erdos911

def ramseyBound : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | s + 1, t + 1 => ramseyBound s (t + 1) + ramseyBound (s + 1) t + 1
termination_by s t => s + t

theorem finite_ramsey (s t : ℕ) {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hS : ramseyBound s t ≤ S.card) :
    (∃ A : Finset V, A ⊆ S ∧ G.IsNClique s A) ∨
    (∃ B : Finset V, B ⊆ S ∧ Gᶜ.IsNClique t B) := by
  classical
  induction s generalizing t S with
  | zero =>
    exact Or.inl ⟨∅, Finset.empty_subset _, SimpleGraph.isNClique_empty.mpr rfl⟩
  | succ s hs =>
    induction t generalizing S with
    | zero =>
      exact Or.inr ⟨∅, Finset.empty_subset _, SimpleGraph.isNClique_empty.mpr rfl⟩
    | succ t ht =>
      have hpos : 0 < S.card := by
        simp only [ramseyBound] at hS
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      let R := (S.erase v).filter (fun w => G.Adj v w)
      let B := (S.erase v).filter (fun w => ¬G.Adj v w)
      have hRsub : R ⊆ S := fun w hw =>
        Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
      have hBsub : B ⊆ S := fun w hw =>
        Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
      by_cases hR : ramseyBound s (t + 1) ≤ R.card
      · rcases hs (t + 1) R hR with ⟨A, hA, hclique⟩ | ⟨A, hA, hclique⟩
        · refine Or.inl ⟨insert v A, ?_, hclique.insert ?_⟩
          · exact Finset.insert_subset hv (hA.trans hRsub)
          · intro w hw
            exact (Finset.mem_filter.mp (hA hw)).2
        · exact Or.inr ⟨A, hA.trans hRsub, hclique⟩
      · have hpartition : R.card + B.card = (S.erase v).card := by
          exact Finset.card_filter_add_card_filter_not (fun w => G.Adj v w)
        have herase : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hv
        have hB : ramseyBound (s + 1) t ≤ B.card := by
          simp only [ramseyBound] at hS
          omega
        rcases ht B hB with ⟨A, hA, hclique⟩ | ⟨A, hA, hclique⟩
        · exact Or.inl ⟨A, hA.trans hBsub, hclique⟩
        · refine Or.inr ⟨insert v A, ?_, hclique.insert ?_⟩
          · exact Finset.insert_subset hv (hA.trans hBsub)
          · intro w hw
            have hwB := Finset.mem_filter.mp (hA hw)
            exact ⟨Ne.symm (Finset.ne_of_mem_erase hwB.1), hwB.2⟩

/-- Every two finite targets admit a finite two-color Ramsey host. -/
theorem finite_ramsey_host {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
      ∀ (R : SimpleGraph (Fin n)), R ≤ F →
        G.IsContained R ∨ H.IsContained (F \ R) := by
  classical
  let n := ramseyBound (Fintype.card α) (Fintype.card β)
  refine ⟨n, ⊤, ?_⟩
  intro R _
  have hG : G.IsContained (⊤ : SimpleGraph (Fin (Fintype.card α))) :=
    SimpleGraph.isContained_top_iff.mpr ⟨(Fintype.equivFin α).toEmbedding⟩
  have hH : H.IsContained (⊤ : SimpleGraph (Fin (Fintype.card β))) :=
    SimpleGraph.isContained_top_iff.mpr ⟨(Fintype.equivFin β).toEmbedding⟩
  rcases finite_ramsey (Fintype.card α) (Fintype.card β) R
      (Finset.univ : Finset (Fin n)) (by simp [n]) with
      ⟨A, _, hA⟩ | ⟨B, _, hB⟩
  · exact Or.inl (hG.trans
      ((SimpleGraph.not_cliqueFree_iff_top_isContained _).mp hA.not_cliqueFree))
  · have hc := hH.trans
      ((SimpleGraph.not_cliqueFree_iff_top_isContained _).mp hB.not_cliqueFree)
    exact Or.inr (by simpa using hc)

end Erdos911
