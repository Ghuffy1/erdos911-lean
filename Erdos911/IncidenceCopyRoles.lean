import Erdos911.PairHostColoring

namespace Erdos911

/-- A bipartite host with a low-degree right side forces every large
left degree of an incidence target to preserve its left/right role. -/
theorem incidence_copy_preserves_roles {L R V : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V]
    (S : R → Finset L) (K H : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel H.Adj]
    (A B : Finset V) (hHK : H ≤ K) (hBip : H.IsBipartiteWith (A : Set V) (B : Set V))
    (D : ℕ) (P : ℝ) (hDP : (D : ℝ) < P)
    (hleft : ∀ x, P ≤ (incidenceGraph S).degree (Sum.inl x))
    (hright : ∀ y, (S y).Nonempty) (hB : ∀ v ∈ B, K.degree v ≤ D)
    (f : (incidenceGraph S).Copy H) :
    (∀ x, f (Sum.inl x) ∈ A) ∧ (∀ y, f (Sum.inr y) ∈ B) := by
  have hleftA (x : L) : f (Sum.inl x) ∈ A := by
    have hdegree : P ≤ (H.degree (f (Sum.inl x)) : ℝ) :=
      (hleft x).trans (by exact_mod_cast f.degree_le (Sum.inl x))
    have hpos : 0 < H.degree (f (Sum.inl x)) := by
      have hpR : (0 : ℝ) < H.degree (f (Sum.inl x)) := by nlinarith only [hDP, hdegree, Nat.cast_nonneg (α := ℝ) D]
      exact_mod_cast hpR
    obtain ⟨v, hv⟩ := (H.degree_pos_iff_exists_adj (f (Sum.inl x))).mp hpos
    rcases hBip.mem_of_adj hv with h | h
    · exact h.1
    · have hmax : H.degree (f (Sum.inl x)) ≤ D :=
        ((SimpleGraph.Copy.ofLE H K hHK).degree_le _).trans (hB _ h.1)
      have hmaxR : (H.degree (f (Sum.inl x)) : ℝ) ≤ D := by exact_mod_cast hmax
      exact (not_lt_of_ge (hdegree.trans hmaxR) hDP).elim
  refine ⟨hleftA, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hright y
  have hxy : H.Adj (f (Sum.inl x)) (f (Sum.inr y)) := map_rel f.toHom hx
  exact hBip.mem_of_mem_adj (hleftA x) hxy

/-- The concrete red host graph has no copy of the incidence target
once the pair-pattern marking avoids every corresponding unmarked copy. -/
theorem pair_host_red_excludes_target {X L R V : Type*}
    [Fintype X] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V]
    (F : SimpleGraph X) (S : R → Finset L) (K : SimpleGraph V) [DecidableRel K.Adj]
    (A B : Finset V) (hAB : Disjoint A B) (D t : ℕ) (P : ℝ) (hDP : (D : ℝ) < P)
    (hleft : ∀ x, P ≤ (incidenceGraph S).degree (Sum.inl x))
    (hright : ∀ y, (S y).Nonempty) (hB : ∀ v ∈ B, K.degree v ≤ D)
    (φ : X → L) (hφ : Function.Injective φ) (ht : 0 < t)
    (hpattern : ∀ u v, F.Adj u v → t ≤ incidenceCodegree S (φ u) (φ v))
    (ω : Sym2 V → Bool)
    (havoid : ∀ f : F.Copy (heavyIncidenceGraph (restrictedHostRows K A B) (t : ℝ)),
      ω ∉ fixedBits (copyRawEdges f) false) :
    ¬(incidenceGraph S).IsContained (pairHostRed K A B ω) := by
  classical
  rintro ⟨g⟩
  obtain ⟨hL, hR⟩ := incidence_copy_preserves_roles S K (pairHostRed K A B ω) A B
    (pairHostRed_le K A B ω) (pairHostRed_bipartite K A B ω hAB) D P hDP hleft hright hB g
  let l : L → V := fun x => g (Sum.inl x)
  let r : R → ↥B := fun y => ⟨g (Sum.inr y), hR y⟩
  have hl : Function.Injective l := fun _ _ h => Sum.inl_injective (g.injective h)
  have hr : Function.Injective r := by
    intro y z h
    exact Sum.inr_injective (g.injective (congrArg Subtype.val h))
  have hred (y : R) (x : L) (hx : x ∈ S y) : l x ∈ pairRedRow (restrictedHostRows K A B (r y)) ω := by
    have hxy := map_rel g.toHom (show (incidenceGraph S).Adj (Sum.inl x) (Sum.inr y) from hx)
    exact (pairHostRed_between_iff K A B ω hAB _ _ (hL x) (hR y)).mp hxy
  obtain ⟨f, hf⟩ := red_incidence_induces_unmarked_pair_copy F S (restrictedHostRows K A B)
    φ hφ l hl r hr t ht hpattern ω hred
  exact havoid f hf

end Erdos911
