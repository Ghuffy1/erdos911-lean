import Erdos911.RestrictedStarDescriptions

namespace Erdos911

noncomputable def onePoolPatterns {E : Type*} [DecidableEq E]
    (U S : Finset E) (a : ℕ) (g : ℝ) : Finset (Finset E) := by
  classical
  exact (U.powersetCard a).filter (fun F => g ≤ (F ∩ S).card)

theorem mem_onePoolPatterns {E : Type*} [DecidableEq E]
    (U S : Finset E) (a : ℕ) (g : ℝ) (F : Finset E) :
    F ∈ onePoolPatterns U S a g ↔ F ⊆ U ∧ F.card = a ∧ g ≤ (F ∩ S).card := by
  classical
  simp only [onePoolPatterns, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

theorem onePoolPatterns_subset_descriptions {E : Type*} [DecidableEq E]
    (U S : Finset E) (a C P : ℕ) (g : ℝ) (hC : 0 < C) (hCP : C ≤ P) :
    onePoolPatterns U S a g ⊆
      restrictedStarDescriptions U (fun _ : Unit => S) (fun _ : Unit => C)
        a a P (g * Real.log ((P : ℝ) / C)) := by
  classical
  intro F hF
  obtain ⟨hFU, hFa, hmass⟩ := (mem_onePoolPatterns U S a g F).mp hF
  let t : Unit → ℕ := fun _ => (F ∩ S).card
  have ht : (F ∩ S).card ≤ a := by
    simpa only [hFa] using Finset.card_le_card (Finset.inter_subset_left (s₁ := F) (s₂ := S))
  have hlog : 0 ≤ Real.log ((P : ℝ) / C) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by exact_mod_cast hC : (0 : ℝ) < C)).mpr
    simpa only [one_mul] using (show (C : ℝ) ≤ P by exact_mod_cast hCP)
  apply (mem_restrictedStarDescriptions U (fun _ : Unit => S) (fun _ : Unit => C) a a P _ F).mpr
  refine ⟨t, (by intro i; exact ht), ?_, ?_, ?_⟩
  · simpa only [t, Fintype.sum_unique] using ht
  · simpa only [t, Fintype.sum_unique] using mul_le_mul_of_nonneg_right hmass hlog
  · apply (mem_restrictedStarSubsets U (fun _ : Unit => S) _ t F).mpr
    refine ⟨F \ (F ∩ S), (fun _ => F ∩ S), Finset.sdiff_subset.trans hFU, ?_, ?_, ?_⟩
    · have h := Finset.card_sdiff_add_card_eq_card
        (Finset.inter_subset_left : F ∩ S ⊆ F)
      simp only [t, Fintype.sum_unique]
      omega
    · intro i
      exact ⟨Finset.inter_subset_right, rfl⟩
    · ext e
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_biUnion,
        Finset.mem_univ, true_and, exists_const]
      tauto

/-- Requiring `g` edges from a pool of size at most `C` saves
`g*log(P/C)` in the exponent, with a uniform linear entropy error. -/
theorem onePoolPatterns_card_bound {E : Type*} [DecidableEq E]
    (U S : Finset E) (a C P : ℕ) (g : ℝ)
    (ha : 0 < a) (hC : 0 < C) (hCP : C ≤ P) (hU : U.card ≤ P) (hS : S.card ≤ C) :
    ((onePoolPatterns U S a g).card : ℝ) ≤
      (a + 1 : ℝ) * Real.exp ((a : ℝ) * Real.log ((P : ℝ) / a) -
        g * Real.log ((P : ℝ) / C) + 2 * a) := by
  have hsub := onePoolPatterns_subset_descriptions U S a C P g hC hCP
  have hcount : ((onePoolPatterns U S a g).card : ℝ) ≤
      (restrictedStarDescriptions U (fun _ : Unit => S) (fun _ : Unit => C)
        a a P (g * Real.log ((P : ℝ) / C))).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hbound := restrictedStarDescriptions_card_bound U (fun _ : Unit => S) (fun _ : Unit => C)
    a a P (g * Real.log ((P : ℝ) / C)) (hC.trans_le hCP) (fun _ => hC)
    (by simp) ha (by simpa using hU) (fun _ => hS)
  exact hcount.trans (by simpa using hbound)

end Erdos911
