import Erdos911.SeedDescriptions
import Erdos911.CandidateRectangles

namespace Erdos911

noncomputable def seedFlagNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) (c : SeedDescription F H s)
    (v : V) : Finset (c.1.val : Set V) := by
  classical
  exact c.2.2.filter (fun u => F.Adj v u.val)

noncomputable def seedHitNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) (w : W) : Finset (c.1.val : Set V) := by
  classical
  exact (seedFlagNeighbors F H s c v).filter (fun u => J.Adj w (c.2.1 u))

theorem mem_seedHitNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) (w : W) (u : (c.1.val : Set V)) :
    u ∈ seedHitNeighbors F H J s c v w ↔
      u ∈ seedFlagNeighbors F H s c v ∧ J.Adj w (c.2.1 u) := by
  classical
  simp only [seedHitNeighbors, Finset.mem_filter]

noncomputable def seedCandidateList {V W : Type*}
    [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ)
    (c : SeedDescription F H s) (v : V) : Finset W := by
  classical
  exact Finset.univ.filter (fun w =>
    (∃ u : (c.1.val : Set V), u.val = v ∧ c.2.1 u = w) ∨
      (v ∉ c.1.val ∧ 0 < (seedFlagNeighbors F H s c v).card ∧
        τ * (seedFlagNeighbors F H s c v).card ≤
          ((seedHitNeighbors F H J s c v w).card : ℝ)))

theorem mem_seedCandidateList {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel J.Adj] (s : ℕ) (τ : ℝ)
    (c : SeedDescription F H s) (v : V) (w : W) :
    w ∈ seedCandidateList F H J s τ c v ↔
      (∃ u : (c.1.val : Set V), u.val = v ∧ c.2.1 u = w) ∨
        (v ∉ c.1.val ∧ 0 < (seedFlagNeighbors F H s c v).card ∧
          τ * (seedFlagNeighbors F H s c v).card ≤
            ((seedHitNeighbors F H J s c v w).card : ℝ)) := by
  classical
  simp only [seedCandidateList, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A candidate either is a seed image or has a retained edge to a flagged
seed image. Both cases anchor the seed in a closed host neighborhood. -/
theorem seedCandidateList_anchor {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (s : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (c : SeedDescription F H s) (v : V) (w : W)
    (hw : w ∈ seedCandidateList F H J s τ c v) :
    c ∈ seedsMeetingAnchors F H s (insert w (H.neighborFinset w)) := by
  classical
  apply (mem_seedsMeetingAnchors F H s _ c).mpr
  rcases (mem_seedCandidateList F H J s τ c v w).mp hw with ⟨u, _, rfl⟩ | ⟨_, hpos, hcount⟩
  · exact ⟨u, Finset.mem_insert_self _ _⟩
  · have hposR : (0 : ℝ) < (seedFlagNeighbors F H s c v).card := by exact_mod_cast hpos
    have hcountpos : 0 < (seedHitNeighbors F H J s c v w).card := by
      exact_mod_cast (mul_pos hτ hposR).trans_le hcount
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hcountpos
    exact ⟨u, Finset.mem_insert_of_mem
      ((H.mem_neighborFinset w (c.2.1 u)).mpr (hJ ((mem_seedHitNeighbors F H J s c v w u).mp hu).2))⟩

noncomputable def seedsWithCandidate {V W : Type*}
    [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (w : W) :
    Finset (SeedDescription F H s) := by
  classical
  exact Finset.univ.filter (fun c => ∃ v, w ∈ seedCandidateList F H J s τ c v)

theorem mem_seedsWithCandidate {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (w : W)
    (c : SeedDescription F H s) :
    c ∈ seedsWithCandidate F H J s τ w ↔ ∃ v, w ∈ seedCandidateList F H J s τ c v := by
  classical
  simp only [seedsWithCandidate, Finset.mem_filter, Finset.mem_univ, true_and]

theorem seedsWithCandidate_card_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s : ℕ) (τ : ℝ) (hτ : 0 < τ) (w : W) :
    (seedsWithCandidate F H J s τ w).card ≤
      Fintype.card V * (D + 1) * ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s) := by
  classical
  have hsub : seedsWithCandidate F H J s τ w ⊆
      seedsMeetingAnchors F H s (insert w (H.neighborFinset w)) := by
    intro c hc
    obtain ⟨v, hv⟩ := (mem_seedsWithCandidate F H J s τ w c).mp hc
    exact seedCandidateList_anchor F H J hJ s τ hτ c v w hv
  have hcard : (insert w (H.neighborFinset w)).card ≤ D + 1 := by
    apply (Finset.card_insert_le _ _).trans
    rw [H.card_neighborFinset_eq_degree]
    exact Nat.add_le_add_right (hD w) 1
  exact (Finset.card_le_card hsub).trans
    ((seedsMeetingAnchors_card_le F H Δ D hΔ hD hΔpos hDpos s _).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcard)))

/-- Simultaneous sample accuracy and the absence of a dense rectangle
bound every list determined by a seed. Seed roles have singleton lists. -/
theorem seedCandidateList_card_lt {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel J.Adj]
    (s : ℕ) (τ ε ρ : ℝ) (c : SeedDescription F H s) (U : V → Finset W)
    (q : ℕ) (hq : 2 ≤ q) (hρ : 0 ≤ ρ)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hU : ∀ v, v ∉ c.1.val → 2 * q ≤ (U v).card)
    (hgap : ∀ v, v ∉ c.1.val → ρ * (U v).card + q < (τ - ε) * (U v).card)
    (haccuracy : ∀ v, v ∉ c.1.val → ∀ w,
      |((seedHitNeighbors F H J s c v w).card : ℝ) /
          (seedFlagNeighbors F H s c v).card -
        (((U v).filter (J.Adj w)).card : ℝ) / (U v).card| ≤ ε)
    (v : V) : (seedCandidateList F H J s τ c v).card < q := by
  classical
  by_cases hv : v ∈ c.1.val
  · have hsub : seedCandidateList F H J s τ c v ⊆ {c.2.1 ⟨v, hv⟩} := by
      intro w hw
      rcases (mem_seedCandidateList F H J s τ c v w).mp hw with ⟨u, huv, huw⟩ | h
      · have hu : u = ⟨v, hv⟩ := Subtype.ext huv
        rw [hu] at huw
        exact Finset.mem_singleton.mpr huw.symm
      · exact (h.1 hv).elim
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  · apply sampled_candidate_list_card_lt J (U v) (seedCandidateList F H J s τ c v)
      (fun w => ((seedHitNeighbors F H J s c v w).card : ℝ) /
        (seedFlagNeighbors F H s c v).card) q ρ τ ε (by omega) hρ (hU v hv) hnodense (hgap v hv)
    · intro w hw
      rcases (mem_seedCandidateList F H J s τ c v w).mp hw with ⟨u, huv, _⟩ | h
      · exact (hv (huv ▸ u.property)).elim
      · exact (le_div_iff₀ (by exact_mod_cast h.2.1)).mpr h.2.2
    · exact fun w _ => haccuracy v hv w

end Erdos911
