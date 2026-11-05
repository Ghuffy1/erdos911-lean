import Erdos911.SeedAssignmentCounting
import Erdos911.UnmarkedSetAvoidance

namespace Erdos911

def seedAssignmentCountBound (k Δ D s q : ℕ) : ℕ :=
  (k * (D + 1) * ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)) * (q + 1) ^ k

noncomputable def largeSeedAssignments {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q b : ℕ) :
    Finset (SeedAssignment F H J s τ q) := by
  classical
  exact Finset.univ.filter (fun a => b ≤ (partialAssignmentEdges F J a.2.val).card)

theorem mem_largeSeedAssignments {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q b : ℕ)
    (a : SeedAssignment F H J s τ q) :
    a ∈ largeSeedAssignments F H J s τ q b ↔ b ≤ (partialAssignmentEdges F J a.2.val).card := by
  classical
  simp only [largeSeedAssignments, Finset.mem_filter, Finset.mem_univ, true_and]

theorem largeSeedAssignments_incidence {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s q b : ℕ) (τ : ℝ) (hτ : 0 < τ) (e : J.edgeSet) :
    (Finset.univ.filter (fun a : largeSeedAssignments F H J s τ q b =>
      e ∈ partialAssignmentEdges F J a.val.2.val)).card ≤
        seedAssignmentCountBound (Fintype.card V) Δ D s q := by
  classical
  exact (subtype_filter_card_le (largeSeedAssignments F H J s τ q b)
    (fun a : SeedAssignment F H J s τ q => e ∈ partialAssignmentEdges F J a.2.val)).trans
    (seed_assignment_edge_incidence F H J hJ Δ D hΔ hD hΔpos hDpos s q τ hτ e)

/-- Marking the residual edges destroys every large seed assignment and
charges at most twice the independent expected number of marked edges. -/
theorem exists_seed_assignment_marks {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (hF : F.Connected)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s q b : ℕ) (τ p : ℝ)
    (hτ : 0 < τ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * seedAssignmentCountBound (Fintype.card V) Δ D s q / p) ≤ p * b / 2) :
    ∃ ω : J.edgeSet → Bool,
      ((Finset.univ.filter (fun e => ω e = true)).card : ℝ) ≤ 2 * p * J.edgeFinset.card ∧
      ∀ a : SeedAssignment F H J s τ q, b ≤ (partialAssignmentEdges F J a.2.val).card →
        ∃ e ∈ partialAssignmentEdges F J a.2.val, ω e = true := by
  classical
  let A := largeSeedAssignments F H J s τ q b
  let supports (a : A) := partialAssignmentEdges F J a.val.2.val
  let N := seedAssignmentCountBound (Fintype.card V) Δ D s q
  have hN : 0 < N := by
    have hk : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hF.nonempty
    have hΔp : 0 < Δ := by omega
    have hDp : 0 < D := by omega
    dsimp only [N, seedAssignmentCountBound]
    positivity
  have hsize : ∀ a : A, b ≤ (supports a).card := fun a =>
    (mem_largeSeedAssignments F H J s τ q b a.val).mp a.property
  have hcount : ∀ e : J.edgeSet,
      (Finset.univ.filter (fun a : A => e ∈ supports a)).card ≤ N := by
    intro e
    exact largeSeedAssignments_incidence F H J hJ Δ D hΔ hD hΔpos hDpos s q b τ hτ e
  obtain ⟨ω, hcost, hhits⟩ := exists_marks_meeting_sets_of_log_bound supports b N hN hsize hcount
    p hp₀ hp₁ hlog
  refine ⟨ω, ?_, ?_⟩
  · simpa only [SimpleGraph.edgeFinset_card] using hcost
  · intro a ha
    exact hhits ⟨a, (mem_largeSeedAssignments F H J s τ q b a).mpr ha⟩

/-- If every test copy supplies a large compatible seed assignment, the
residual marking gives a concrete subgraph with no test copy. -/
theorem exists_seed_assignment_obstruction {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (hF : F.Connected)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s q b : ℕ) (τ p : ℝ)
    (hτ : 0 < τ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * seedAssignmentCountBound (Fintype.card V) Δ D s q / p) ≤ p * b / 2)
    (hcoverage : ∀ f : F.Copy H, ∃ a : SeedAssignment F H J s τ q,
      PartialAssignmentAgrees a.2.val f ∧ b ≤ (partialAssignmentEdges F J a.2.val).card) :
    ∃ marked : Finset (Sym2 W), marked ⊆ J.edgeFinset ∧
      (marked.card : ℝ) ≤ 2 * p * J.edgeFinset.card ∧
        ¬F.IsContained (H.deleteEdges (marked : Set (Sym2 W))) := by
  classical
  obtain ⟨ω, hcost, hhits⟩ := exists_seed_assignment_marks F H J hJ hF Δ D hΔ hD hΔpos hDpos
    s q b τ p hτ hp₀ hp₁ hlog
  let marked := (Finset.univ.filter (fun e : J.edgeSet => ω e = true)).map
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : marked ⊆ J.edgeFinset := by
    intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp he
    exact (J.mem_edgeFinset).mpr a.property
  refine ⟨marked, hsub, ?_, ?_⟩
  · simpa only [marked, Finset.card_map] using hcost
  · rintro ⟨f⟩
    let fH : F.Copy H := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
    obtain ⟨a, hagree, hlarge⟩ := hcoverage fH
    obtain ⟨e, he, htrue⟩ := hhits a hlarge
    have hecopy := partialAssignmentEdges_subset_copy J a.2.val fH hagree e he
    rw [copyRawEdges_ofLE_comp] at hecopy
    have heremains := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e.val).mp hecopy)
    rw [H.edgeSet_deleteEdges] at heremains
    apply heremains.2
    exact Finset.mem_map.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrue⟩, rfl⟩

end Erdos911
