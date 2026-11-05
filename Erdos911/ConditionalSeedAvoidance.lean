import Erdos911.SeedResidualColoring

namespace Erdos911

noncomputable def seedAssignmentGood {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q b : ℕ) :
    Set (J.edgeSet → Bool) :=
  avoidAll (fun a : largeSeedAssignments F H J s τ q b =>
    fixedBits (partialAssignmentEdges F J a.val.2.val) false)

theorem seedAssignmentGood_hits {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q b : ℕ)
    (ω : J.edgeSet → Bool) (hω : ω ∈ seedAssignmentGood F H J s τ q b)
    (a : SeedAssignment F H J s τ q) (ha : b ≤ (partialAssignmentEdges F J a.2.val).card) :
    ∃ e ∈ partialAssignmentEdges F J a.2.val, ω e = true := by
  classical
  by_contra hn
  apply hω ⟨a, (mem_largeSeedAssignments F H J s τ q b a).mpr ha⟩
  intro e he
  have hne : ω e ≠ true := fun ht => hn ⟨e, he, ht⟩
  cases hval : ω e <;> simp_all

theorem seed_assignment_conditional_avoidance {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H) (hF : F.Connected)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s q b : ℕ) (τ p : ℝ)
    (hτ : 0 < τ) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hlog : Real.log (8 * seedAssignmentCountBound (Fintype.card V) Δ D s q / p) ≤ p * b / 2) :
    0 < (bitProductMeasure J.edgeSet p hp₀.le hp₁).real (seedAssignmentGood F H J s τ q b) ∧
      ∀ T : Finset J.edgeSet, (bitProductMeasure J.edgeSet p hp₀.le hp₁).real
        (fixedBits T true ∩ seedAssignmentGood F H J s τ q b) /
          (bitProductMeasure J.edgeSet p hp₀.le hp₁).real (seedAssignmentGood F H J s τ q b) ≤
            (p * Real.exp (p / 4)) ^ T.card := by
  classical
  let A := largeSeedAssignments F H J s τ q b
  let supports (a : A) := partialAssignmentEdges F J a.val.2.val
  let N := seedAssignmentCountBound (Fintype.card V) Δ D s q
  have hN : 0 < N := by
    have hk : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hF.nonempty
    dsimp only [N, seedAssignmentCountBound]
    positivity
  have hsize : ∀ a : A, b ≤ (supports a).card := fun a =>
    (mem_largeSeedAssignments F H J s τ q b a.val).mp a.property
  have hcount : ∀ e : J.edgeSet,
      (Finset.univ.filter (fun a : A => e ∈ supports a)).card ≤ N :=
    fun e => largeSeedAssignments_incidence F H J hJ Δ D hΔ hD hΔpos hDpos s q b τ hτ e
  exact unmarked_sets_avoidance_of_log_bound supports b N hN hsize hcount p hp₀ hp₁ hlog

/-- Avoidance of the large assignment events rules out the test graph
after the marked residual edges are removed. -/
theorem seedAssignmentGood_no_copy {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q b : ℕ)
    (hcoverage : ∀ f : F.Copy H, ∃ a : SeedAssignment F H J s τ q,
      PartialAssignmentAgrees a.2.val f ∧ b ≤ (partialAssignmentEdges F J a.2.val).card)
    (ω : J.edgeSet → Bool) (hω : ω ∈ seedAssignmentGood F H J s τ q b) :
    ¬F.IsContained (H \ edgeColorClass J ω true) := by
  classical
  rintro ⟨f⟩
  let fH : F.Copy H := (SimpleGraph.Copy.ofLE _ H sdiff_le).comp f
  obtain ⟨a, hagree, hlarge⟩ := hcoverage fH
  obtain ⟨e, he, htrue⟩ := seedAssignmentGood_hits F H J s τ q b ω hω a hlarge
  have hecopy := partialAssignmentEdges_subset_copy J a.2.val fH hagree e he
  rw [copyRawEdges_ofLE_comp] at hecopy
  have heremains := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e.val).mp hecopy)
  rw [SimpleGraph.edgeSet_sdiff] at heremains
  exact heremains.2 ((edgeColorClass_edge_iff J ω true e).mpr htrue)

end Erdos911
