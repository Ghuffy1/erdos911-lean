import Erdos911.TolerantSeedLists
import Erdos911.HighLowHost

namespace Erdos911

noncomputable def seedHighFlagNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H : SimpleGraph W) (high : Finset W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) : Finset (c.1.val : Set V) := by
  classical
  exact (seedFlagNeighbors F H s c v).filter (fun u => c.2.1 u ∈ high)

noncomputable def seedHighHitNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H J : SimpleGraph W) (high : Finset W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) (w : W) : Finset (c.1.val : Set V) := by
  classical
  exact (seedHighFlagNeighbors F H high s c v).filter (fun u => J.Adj w (c.2.1 u))

theorem mem_seedHighFlagNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H : SimpleGraph W) (high : Finset W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) (u : (c.1.val : Set V)) :
    u ∈ seedHighFlagNeighbors F H high s c v ↔
      u ∈ seedFlagNeighbors F H s c v ∧ c.2.1 u ∈ high := by
  classical
  exact Finset.mem_filter

theorem mem_seedHighHitNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H J : SimpleGraph W) (high : Finset W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) (w : W) (u : (c.1.val : Set V)) :
    u ∈ seedHighHitNeighbors F H J high s c v w ↔
      u ∈ seedHighFlagNeighbors F H high s c v ∧ J.Adj w (c.2.1 u) := by
  classical
  exact Finset.mem_filter

/-- Only right roles passing the sampled high-neighbor test have lists.
Their candidates lie on the low side of the fixed host partition. -/
noncomputable def incidenceCandidateList {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (right : Finset V) (high : Finset W)
    (d s : ℕ) (α τ : ℝ) (c : SeedDescription F H s) (v : V) : Finset W := by
  classical
  exact Finset.univ.filter (fun w =>
    v ∈ right ∧ v ∉ c.1.val ∧ 0 < (seedHighFlagNeighbors F H high s c v).card ∧
      α * d / 3 ≤ (seedHighFlagNeighbors F H high s c v).card ∧ w ∉ high ∧
      τ * (seedHighFlagNeighbors F H high s c v).card ≤ (seedHighHitNeighbors F H J high s c v w).card)

theorem mem_incidenceCandidateList {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (right : Finset V) (high : Finset W)
    (d s : ℕ) (α τ : ℝ) (c : SeedDescription F H s) (v : V) (w : W) :
    w ∈ incidenceCandidateList F H J right high d s α τ c v ↔
      v ∈ right ∧ v ∉ c.1.val ∧ 0 < (seedHighFlagNeighbors F H high s c v).card ∧
        α * d / 3 ≤ (seedHighFlagNeighbors F H high s c v).card ∧ w ∉ high ∧
        τ * (seedHighFlagNeighbors F H high s c v).card ≤ (seedHighHitNeighbors F H J high s c v w).card := by
  classical
  simp only [incidenceCandidateList, Finset.mem_filter, Finset.mem_univ, true_and]

theorem seedHighFlagNeighbors_subset {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H : SimpleGraph W) (high : Finset W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) :
    seedHighFlagNeighbors F H high s c v ⊆ seedFlagNeighbors F H s c v := by
  classical
  exact Finset.filter_subset _ _

theorem seedHighHitNeighbors_subset {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H J : SimpleGraph W) (high : Finset W) (s : ℕ)
    (c : SeedDescription F H s) (v : V) (w : W) :
    seedHighHitNeighbors F H J high s c v w ⊆ seedHitNeighbors F H J s c v w := by
  classical
  intro u hu
  obtain ⟨huflag, huJ⟩ := Finset.mem_filter.mp hu
  exact (mem_seedHitNeighbors F H J s c v w u).mpr
    ⟨seedHighFlagNeighbors_subset F H high s c v huflag, huJ⟩

theorem seedFlagNeighbors_card_le_seed_bound {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) (c : SeedDescription F H s) (v : V) :
    (seedFlagNeighbors F H s c v).card ≤ s := by
  classical
  have h := Finset.card_le_univ (seedFlagNeighbors F H s c v)
  have hcard : Fintype.card (c.1.val : Set V) = c.1.val.card := by simp
  rw [hcard] at h
  exact h.trans c.1.property.1

theorem incidence_candidate_high_hit {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (right : Finset V) (high : Finset W)
    (d s : ℕ) (α τ : ℝ) (hτ : 0 < τ) (c : SeedDescription F H s) (v : V) (w : W)
    (hw : w ∈ incidenceCandidateList F H J right high d s α τ c v) :
    ∃ u : (c.1.val : Set V), u ∈ seedHighFlagNeighbors F H high s c v ∧ J.Adj w (c.2.1 u) := by
  classical
  obtain ⟨_, _, hpositive, _, _, hscore⟩ := (mem_incidenceCandidateList F H J right high d s α τ c v w).mp hw
  have hposR : (0 : ℝ) < (seedHighFlagNeighbors F H high s c v).card := by exact_mod_cast hpositive
  have hhit : 0 < (seedHighHitNeighbors F H J high s c v w).card := by
    exact_mod_cast (mul_pos hτ hposR).trans_le hscore
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hhit
  exact ⟨u, Finset.mem_filter.mp hu⟩

/-- A positive high-neighbor score anchors the seed in the ordinary
candidate family at threshold `1/(s+1)`, independently of the sampling rate. -/
theorem incidenceCandidateList_subset_seedCandidateList {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel J.Adj]
    (right : Finset V) (high : Finset W) (d s : ℕ) (α τ : ℝ) (hτ : 0 < τ)
    (c : SeedDescription F H s) (v : V) :
    incidenceCandidateList F H J right high d s α τ c v ⊆
      seedCandidateList F H J s (1 / ((s : ℝ) + 1)) c v := by
  classical
  intro w hw
  have hv := ((mem_incidenceCandidateList F H J right high d s α τ c v w).mp hw).2.1
  obtain ⟨u, huHigh, huJ⟩ := incidence_candidate_high_hit F H J right high d s α τ hτ c v w hw
  have huFlag := seedHighFlagNeighbors_subset F H high s c v huHigh
  have hflag : 0 < (seedFlagNeighbors F H s c v).card := Finset.card_pos.mpr ⟨u, huFlag⟩
  have hhit : 1 ≤ (seedHitNeighbors F H J s c v w).card :=
    Finset.one_le_card.mpr ⟨u, (mem_seedHitNeighbors F H J s c v w u).mpr ⟨huFlag, huJ⟩⟩
  have hbound : ((seedFlagNeighbors F H s c v).card : ℝ) ≤ s := by
    exact_mod_cast seedFlagNeighbors_card_le_seed_bound F H s c v
  have hsmall : (1 / ((s : ℝ) + 1)) * (seedFlagNeighbors F H s c v).card ≤ 1 := by
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr (by linarith)
  apply (mem_seedCandidateList F H J s _ c v w).mpr
  exact Or.inr ⟨hv, hflag, hsmall.trans (by exact_mod_cast hhit)⟩

theorem incidence_candidate_actual_high_neighbor {V W : Type*}
    [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (right : Finset V) (high : Finset W)
    (d s : ℕ) (α τ : ℝ) (hτ : 0 < τ) (c : SeedDescription F H s)
    (f : F.Copy H) (hagree : seedMapAgrees F H s c f) (v : V) (w : W)
    (hw : w ∈ incidenceCandidateList F H J right high d s α τ c v) :
    ∃ u, F.Adj v u ∧ f u ∈ high := by
  classical
  obtain ⟨u, huHigh, _⟩ := incidence_candidate_high_hit F H J right high d s α τ hτ c v w hw
  obtain ⟨huFlag, huHigh⟩ := Finset.mem_filter.mp huHigh
  have huAdj : F.Adj v u.val := (Finset.mem_filter.mp huFlag).2
  rw [hagree u] at huHigh
  exact ⟨u.val, huAdj, huHigh⟩

end Erdos911
