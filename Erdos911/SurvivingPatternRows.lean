import Erdos911.PatternFiberCounts

namespace Erdos911

noncomputable def survivingPatternRows {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (Low : R → Prop) [DecidablePred Low] (b M : ℕ) : Finset R :=
  U.filter (fun y => Low y ∧ b ≤ 8 * M * (patternFiber U f (f y)).card ∧
    (patternFiber U f (f y)).card ≤ 2 * ((patternFiber U f (f y)).filter Low).card)

theorem mem_survivingPatternRows {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (Low : R → Prop) [DecidablePred Low] (b M : ℕ) (y : R) :
    y ∈ survivingPatternRows U f Low b M ↔ y ∈ U ∧ Low y ∧
      b ≤ 8 * M * (patternFiber U f (f y)).card ∧
      (patternFiber U f (f y)).card ≤ 2 * ((patternFiber U f (f y)).filter Low).card := by
  classical
  exact Finset.mem_filter

/-- After rare patterns, low-poor patterns and high images are removed,
at least three eighths of the reference number of rows remain. -/
theorem survivingPatternRows_card_bound {R P : Type*} [DecidableEq P]
    (U : Finset R) (f : R → P) (Low : R → Prop) [DecidablePred Low]
    (b M : ℕ) (hM : 0 < M) (hcount : (U.image f).card ≤ M)
    (hU : 7 * b ≤ 8 * U.card) (hhigh : 8 * (U.filter (fun y => ¬Low y)).card ≤ b) :
    3 * b ≤ 8 * (survivingPatternRows U f Low b M).card := by
  classical
  let G := survivingPatternRows U f Low b M
  let L := lightPatternRows U f b M
  let P := poorLowPatternRows U f Low
  let H := U.filter (fun y => ¬Low y)
  have hcover : U ⊆ G ∪ L ∪ P ∪ H := by
    intro y hy
    by_cases hlo : Low y
    · by_cases hfreq : b ≤ 8 * M * (patternFiber U f (f y)).card
      · by_cases hrich : (patternFiber U f (f y)).card ≤ 2 * ((patternFiber U f (f y)).filter Low).card
        · have hm : y ∈ G := (mem_survivingPatternRows U f Low b M y).mpr ⟨hy, hlo, hfreq, hrich⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
        · have hm : y ∈ P := Finset.mem_filter.mpr ⟨hy, by omega⟩
          exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · have hm : y ∈ L := Finset.mem_filter.mpr ⟨hy, by omega⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hlo⟩)
  have hc := Finset.card_le_card hcover
  have h₁ := Finset.card_union_le (G ∪ L ∪ P) H
  have h₂ := Finset.card_union_le (G ∪ L) P
  have h₃ := Finset.card_union_le G L
  have hmass : U.card ≤ G.card + L.card + P.card + H.card := by omega
  have hlight := lightPatternRows_card_bound U f b M hM hcount
  have hpoor := poorLowPatternRows_card_bound U f Low
  change 3 * b ≤ 8 * G.card
  change 8 * L.card ≤ b at hlight
  change P.card ≤ 2 * H.card at hpoor
  change 8 * H.card ≤ b at hhigh
  omega

end Erdos911
