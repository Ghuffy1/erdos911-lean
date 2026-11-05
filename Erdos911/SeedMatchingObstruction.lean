import Erdos911.SeededRedCopyExclusion
import Erdos911.ThickMatchingEvents

namespace Erdos911

theorem copy_deleteEdges_disjoint {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H : SimpleGraph W) (K : Finset (Sym2 W))
    (f : F.Copy (H.deleteEdges (K : Set (Sym2 W)))) :
    Disjoint (copyRawEdges ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) K := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hK
  have hecopy : e ∈ copyRawEdges f := by simpa only [copyRawEdges_ofLE_comp] using he
  have hehost := f.toSubgraph.edgeSet_subset ((mem_copyRawEdges_iff f e).mp hecopy)
  rw [H.edgeSet_deleteEdges] at hehost
  exact hehost.2 hK

theorem seeded_copy_thickMatchingEvent {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : F.Copy H) (s r : ℕ) (τ T u : ℝ) (hτ : 0 < τ)
    (c : SeedDescription F H s) (B : I → Finset W) (h : ℕ)
    (marks : (Fin h × I) → Bool)
    (havoid : Disjoint (copyRawEdges f) (incidentEdgesAtSet H (roundMarkedVertices B h marks)))
    (E : Finset V) (hE : (E.card : ℝ) ≤ u)
    (htrue : ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v) :
    marks ∈ thickMatchingEvent J (unseededCandidateList F H J s τ c) r T B h u := by
  let L := unseededCandidateList F H J s τ c
  let matching := maximumListMatching (fun v : thickCandidateRoles J L r T => L v.val)
  let role := fun k : matchedRoles matching => k.val.val
  have hrole : Function.Injective role := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  exact (seeded_copy_few_blocked F H J f s τ hτ c B h marks havoid E htrue role hrole).trans hE

/-- Avoiding every seed matching event rules out a red test copy once
each copy has a sampled certificate with a bounded exceptional set. -/
theorem no_copy_of_seed_matching_events {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I]
    (F : SimpleGraph V) (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj]
    (s r : ℕ) (τ T u : ℝ) (hτ : 0 < τ)
    (C : Finset (SeedDescription F H s)) (B : I → Finset W) (h : ℕ)
    (marks : (Fin h × I) → Bool)
    (hmarks : ∀ c : C, marks ∉ thickMatchingEvent J (unseededCandidateList F H J s τ c.val) r T B h u)
    (hcertificate : ∀ f : F.Copy H, ∃ c ∈ C, ∃ E : Finset V,
      (E.card : ℝ) ≤ u ∧ ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v) :
    ¬F.IsContained (H.deleteEdges
      (incidentEdgesAtSet H (roundMarkedVertices B h marks) : Set (Sym2 W))) := by
  rintro ⟨f⟩
  let fH := (SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f
  obtain ⟨c, hc, E, hE, htrue⟩ := hcertificate fH
  exact hmarks ⟨c, hc⟩ (seeded_copy_thickMatchingEvent F H J fH s r τ T u hτ c B h marks
    (copy_deleteEdges_disjoint F H _ f) E hE htrue)

noncomputable def largeMatchingSeeds {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s r q m : ℕ) (τ T : ℝ) :
    Finset (SeedDescription F H s) := by
  classical
  exact Finset.univ.filter (fun c =>
    (∀ v, (unseededCandidateList F H J s τ c v).card ≤ q) ∧
    m ≤ (matchedRoles (maximumListMatching (fun v :
      thickCandidateRoles J (unseededCandidateList F H J s τ c) r T =>
        unseededCandidateList F H J s τ c v.val))).card)

theorem mem_largeMatchingSeeds {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s r q m : ℕ) (τ T : ℝ)
    (c : SeedDescription F H s) :
    c ∈ largeMatchingSeeds F H J s r q m τ T ↔
      (∀ v, (unseededCandidateList F H J s τ c v).card ≤ q) ∧
      m ≤ (matchedRoles (maximumListMatching (fun v :
        thickCandidateRoles J (unseededCandidateList F H J s τ c) r T =>
          unseededCandidateList F H J s τ c v.val))).card := by
  classical
  simp only [largeMatchingSeeds, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Tolerant sampling and star-deficit pruning provide the exact
certificate required by the red-copy exclusion theorem. -/
theorem tolerant_copy_matching_certificate {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hF : F.Connected) (hJ : J ≤ H) (f : F.Copy H) (d D Δ s q r P m : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hΔ : ∀ v, F.degree v ≤ Δ) (hΔpos : 0 < Δ) (hhost : ∀ w, H.degree w ≤ D)
    (hq : 2 ≤ q) (hsmall : 2 * q ≤ d) (hP : 0 < P)
    (ρ α ε T u : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (hε₀ : 0 < ε) (hε₁ : ε < 1 / 5) (hT : 0 < T) (hTP : T < P)
    (hgap : ρ * d + q < (1 - 5 * ε) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-(ε ^ 2 * (α * d)) / 128)) ≤ s)
    (htuple : (r : ℝ) * (5 * ε) ≤ 1 / 2)
    (hgood : ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) r P
      ((F.edgeSet.ncard : ℝ) / 32 * Real.log ((P : ℝ) / T)))
    (hcost : 2 * (Δ : ℝ) * (s + (F \ copyRetainedGraph J f).edgeSet.ncard / (ε * d)) ≤
      (F.edgeSet.ncard : ℝ) / 2)
    (hmass : (m : ℝ) * Δ ≤ F.edgeSet.ncard)
    (hexception : s + (F \ copyRetainedGraph J f).edgeSet.ncard / (ε * d) ≤ u) :
    ∃ c ∈ largeMatchingSeeds F H J s r q m (1 - 4 * ε) T, ∃ E : Finset (Fin n),
      (E.card : ℝ) ≤ u ∧ ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s (1 - 4 * ε) c v := by
  obtain ⟨c, hsize, hmatched, htrue, hE⟩ := exists_tolerant_seed_matching F H J hF hJ f
    d D Δ s q r P hd hmin hmax hΔ hhost hq hsmall hP ρ α ε T hρ hα₀ hα₁ hε₀ hε₁ hT hTP
    hgap hnodense hseed htuple hgood hcost
  have hm : m ≤ (matchedRoles (maximumListMatching (fun v :
      thickCandidateRoles J (unseededCandidateList F H J s (1 - 4 * ε) c) r T =>
        unseededCandidateList F H J s (1 - 4 * ε) c v.val))).card := by
    have hΔR : (0 : ℝ) < Δ := by exact_mod_cast hΔpos
    have hmR := hmass.trans hmatched
    have hm' := (mul_le_mul_iff_of_pos_left hΔR).mp
      ((le_of_eq (mul_comm (Δ : ℝ) (m : ℝ))).trans hmR)
    exact_mod_cast hm'
  exact ⟨c, (mem_largeMatchingSeeds F H J s r q m (1 - 4 * ε) T c).mpr ⟨hsize, hm⟩,
    _, hE.trans hexception, htrue⟩

end Erdos911
