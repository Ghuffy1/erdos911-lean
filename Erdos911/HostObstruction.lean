import Erdos911.FiniteRamsey
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace Erdos911

/-- Every red subgraph leaves a copy of the corresponding target in one color. -/
def RamseyFor {α β V : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    (F : SimpleGraph V) : Prop :=
  ∀ R : SimpleGraph V, R ≤ F → G.IsContained R ∨ H.IsContained (F \ R)

theorem sizeRamsey_attained {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) :
    ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
      F.edgeSet.ncard = SimpleGraph.sizeRamsey G H ∧ RamseyFor G H F := by
  obtain ⟨n, F, hF⟩ := finite_ramsey_host G H
  have hnonempty : {m : ℕ | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
      F.edgeSet.ncard = m ∧ RamseyFor G H F}.Nonempty :=
    ⟨F.edgeSet.ncard, n, F, rfl, hF⟩
  exact Nat.sInf_mem hnonempty

theorem sizeRamsey_le_of_host {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) {n : ℕ}
    (F : SimpleGraph (Fin n)) (hF : RamseyFor G H F) :
    SimpleGraph.sizeRamsey G H ≤ F.edgeSet.ncard :=
  Nat.sInf_le ⟨n, F, rfl, hF⟩

theorem sizeRamsey_mono {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    {G : SimpleGraph α} {H : SimpleGraph β}
    {G' : SimpleGraph γ} {H' : SimpleGraph δ}
    (hG : G'.IsContained G) (hH : H'.IsContained H) :
    SimpleGraph.sizeRamsey G' H' ≤ SimpleGraph.sizeRamsey G H := by
  obtain ⟨n, F, hsize, hF⟩ := sizeRamsey_attained G H
  rw [← hsize]
  apply sizeRamsey_le_of_host
  intro R hR
  exact (hF R hR).imp (fun h => hG.trans h) (fun h => hH.trans h)

/-- Exact equivalence between a real-valued lower bound and avoiding colorings
for every host at or below that budget. Strictness and both colors are retained. -/
theorem sizeRamsey_real_gt_iff {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) (M : ℝ) :
    M < (SimpleGraph.sizeRamsey G H : ℝ) ↔
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)), (F.edgeSet.ncard : ℝ) ≤ M →
        ∃ (R : SimpleGraph (Fin n)), R ≤ F ∧
          ¬G.IsContained R ∧ ¬H.IsContained (F \ R) := by
  classical
  constructor
  · intro hM n F hsize
    by_contra hno
    have hF : RamseyFor G H F := by
      intro R hR
      by_contra hneither
      exact hno ⟨R, hR, fun h => hneither (Or.inl h), fun h => hneither (Or.inr h)⟩
    have hle : (SimpleGraph.sizeRamsey G H : ℝ) ≤ F.edgeSet.ncard := by
      exact_mod_cast sizeRamsey_le_of_host G H F hF
    exact (not_lt_of_ge (hle.trans hsize)) hM
  · intro havoids
    obtain ⟨n, F, hsize, hF⟩ := sizeRamsey_attained G H
    by_contra hM
    have hbudget : (F.edgeSet.ncard : ℝ) ≤ M := by
      rw [hsize]
      exact le_of_not_gt hM
    obtain ⟨R, hR, hred, hblue⟩ := havoids n F hbudget
    exact (hF R hR).elim hred hblue

end Erdos911
