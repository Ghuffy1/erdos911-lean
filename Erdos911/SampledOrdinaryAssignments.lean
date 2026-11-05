import Erdos911.CopySeedSamples
import Erdos911.SeedResidualColoring

namespace Erdos911

theorem copy_neighbor_images_card {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (v : V) : ((F.neighborFinset v).image f).card = F.degree v := by
  rw [Finset.card_image_of_injective _ (show Function.Injective (f : V → W) from f.injective),
    F.card_neighborFinset_eq_degree]

theorem copy_candidateSlice_card {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) (v : Fin n) (w : W) :
    (candidateSlice (F.neighborFinset v) (fun j => J.neighborFinset (f j)) w).card =
      (((F.neighborFinset v).image f).filter (J.Adj w)).card := by
  have heq : candidateSlice (F.neighborFinset v) (fun j => J.neighborFinset (f j)) w =
      (F.neighborFinset v).filter (fun j => J.Adj w (f j)) := by
    ext j
    simp only [candidateSlice, Finset.mem_filter, SimpleGraph.mem_neighborFinset, J.adj_comm]
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (show Function.Injective (f : Fin n → W) from f.injective), heq]

theorem copy_self_candidateSlice_card {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) (v : Fin n) :
    (candidateSlice (F.neighborFinset v) (fun j => J.neighborFinset (f j)) (f v)).card =
      (copyRetainedGraph J f).degree v := by
  rw [copyRetainedGraph_degree_eq]
  congr 1
  ext j
  simp only [candidateSlice, Finset.mem_filter, SimpleGraph.mem_neighborFinset, J.adj_comm]

/-- The sampled connected seed provides bounded lists containing every
ordinary role's true image. Its induced partial assignment retains the
quantified edge mass needed for the residual event. -/
theorem exists_ordinary_seed_assignment {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : F.Copy H) (hF : F.Connected) (hJ : J ≤ H) (d D s q : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hq : 2 ≤ q) (hsmall : 2 * q ≤ d)
    (ρ α : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (hgap : ρ * d + q < (11 / 16 : ℝ) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-((1 / 16 : ℝ) ^ 2 * (α * d)) / 128)) ≤ s) :
    ∃ a : SeedAssignment F H J s (3 / 4) q,
      PartialAssignmentAgrees a.2.val f ∧
        F.edgeFinset.card ≤ (partialAssignmentEdges F J a.2.val).card +
          17 * (F \ copyRetainedGraph J f).edgeFinset.card := by
  classical
  let N := fun j => J.neighborFinset (f j)
  have hN : ∀ j, (N j).card ≤ D := by
    intro j
    exact ((SimpleGraph.Copy.ofLE J H hJ).degree_le (f j)).trans (hhost (f j))
  obtain ⟨ω, S, hflags, hconn, haccurate, hsize⟩ := exists_accurate_connected_seed F hF N d D
    hd hmin hmax hN α (1 / 16) hα₀ hα₁ (by norm_num) (by norm_num)
  have hScard : S.card ≤ s := by exact_mod_cast hsize.trans hseed
  let c := seedDescriptionOfCopy f S s hScard hconn ω
  have hU (v : Fin n) : ((F.neighborFinset v).image f).card = F.degree v := copy_neighbor_images_card f v
  have haccuracy : ∀ v, v ∉ S → ∀ w,
      ((seedFlagNeighbors F H s c v).card : ℝ) = sampleCount (F.neighborFinset v) ω ∧
      ((seedHitNeighbors F H J s c v w).card : ℝ) = sampleCount (candidateSlice (F.neighborFinset v) N w) ω := by
    intro v _ w
    exact ⟨copy_seed_flag_count f S s hScard hconn ω hflags v,
      copy_seed_hit_count J f S s hScard hconn ω hflags v w⟩
  have hlistBound : ∀ v, (seedCandidateList F H J s (3 / 4) c v).card ≤ q := by
    intro v
    apply (seedCandidateList_card_lt F H J s (3 / 4) (1 / 16) ρ c
      (fun v => (F.neighborFinset v).image f) q hq hρ hnodense ?_ ?_ ?_ v).le
    · intro u _
      rw [hU]
      exact hsmall.trans (hmin u)
    · intro u _
      rw [hU]
      have hdeg : (d : ℝ) ≤ F.degree u := by exact_mod_cast hmin u
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      have hcoefficient : 0 ≤ (11 / 16 : ℝ) - ρ := by
        nlinarith [Nat.cast_nonneg (α := ℝ) q]
      have hscale := mul_le_mul_of_nonneg_left hdeg hcoefficient
      norm_num
      nlinarith
    · intro u hu w
      obtain ⟨hden, hnum⟩ := haccuracy u hu w
      rw [hden, hnum, ← copy_candidateSlice_card J f u w, hU]
      exact (haccurate u hu).2 w
  have hassignment : ordinaryCopyAssignment J f ∈
      partialListAssignments (seedCandidateList F H J s (3 / 4) c) := by
    apply (mem_partialListAssignments _ _).mpr
    intro v w hw
    have hvalue : f v = w := ordinaryCopyAssignment_agrees J f v w hw
    rw [← hvalue]
    apply (mem_seedCandidateList F H J s (3 / 4) c v (f v)).mpr
    by_cases hvS : v ∈ S
    · exact Or.inl ⟨⟨v, hvS⟩, rfl, rfl⟩
    · have hvOrd : v ∉ exceptionalRoles F (copyRetainedGraph J f) := by
        intro hv
        simp only [ordinaryCopyAssignment, ite_eq_left hv, reduceCtorEq] at hw
      have hretained : 7 * F.degree v ≤ 8 * (copyRetainedGraph J f).degree v := by
        exact Nat.le_of_not_gt (fun h => hvOrd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      have hdegreepos : (0 : ℝ) < F.degree v := by exact_mod_cast hd.trans_le (hmin v)
      have hretainedR : (7 : ℝ) * F.degree v ≤ 8 * (copyRetainedGraph J f).degree v := by
        exact_mod_cast hretained
      have hfraction : (7 / 8 : ℝ) ≤
          ((copyRetainedGraph J f).degree v : ℝ) / F.degree v := by
        apply (le_div_iff₀ hdegreepos).mpr
        nlinarith
      have hgood := haccurate v hvS
      have hscore := hgood.2 (f v)
      rw [copy_self_candidateSlice_card J f v] at hscore
      have hthreshold : (3 / 4 : ℝ) ≤ sampleCount (candidateSlice (F.neighborFinset v) N (f v)) ω /
          sampleCount (F.neighborFinset v) ω := by
        linarith [(abs_le.mp hscore).1]
      obtain ⟨hden, hnum⟩ := haccuracy v hvS (f v)
      refine Or.inr ⟨hvS, ?_, ?_⟩
      · exact_mod_cast (show (0 : ℝ) < (seedFlagNeighbors F H s c v).card by rw [hden]; exact hgood.1)
      · rw [hden, hnum]
        exact (le_div_iff₀ hgood.1).mp hthreshold
  let a : SeedAssignment F H J s (3 / 4) q :=
    ⟨⟨c, (mem_boundedSeedDescriptions F H J s (3 / 4) q c).mpr hlistBound⟩,
      ⟨ordinaryCopyAssignment J f, hassignment⟩⟩
  exact ⟨a, ordinaryCopyAssignment_agrees J f, ordinaryCopyAssignment_edge_count J f⟩

theorem ordinary_seed_assignment_coverage {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hF : F.Connected) (hJ : J ≤ H) (d D s q b : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hq : 2 ≤ q) (hsmall : 2 * q ≤ d)
    (ρ α : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (hgap : ρ * d + q < (11 / 16 : ℝ) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-((1 / 16 : ℝ) ^ 2 * (α * d)) / 128)) ≤ s)
    (hlarge : ∀ f : F.Copy H, b + 17 * (F \ copyRetainedGraph J f).edgeFinset.card ≤ F.edgeFinset.card) :
    ∀ f : F.Copy H, ∃ a : SeedAssignment F H J s (3 / 4) q,
      PartialAssignmentAgrees a.2.val f ∧ b ≤ (partialAssignmentEdges F J a.2.val).card := by
  intro f
  obtain ⟨a, hagree, hmass⟩ := exists_ordinary_seed_assignment F H J f hF hJ d D s q
    hd hmin hmax hhost hq hsmall ρ α hρ hα₀ hα₁ hgap hnodense hseed
  refine ⟨a, hagree, ?_⟩
  have hbudget := hlarge f
  omega

theorem finite_sparse_residual_obstruction {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hF : F.Connected) (hJ : J ≤ H) (d D s q b : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hD : 1 ≤ D) (hq : 2 ≤ q) (hsmall : 2 * q ≤ d)
    (ρ α p : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hgap : ρ * d + q < (11 / 16 : ℝ) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-((1 / 16 : ℝ) ^ 2 * (α * d)) / 128)) ≤ s)
    (hlarge : ∀ f : F.Copy H, b + 17 * (F \ copyRetainedGraph J f).edgeFinset.card ≤ F.edgeFinset.card)
    (hlog : Real.log (8 * seedAssignmentCountBound n D D s q / p) ≤ p * b / 2) :
    ∃ marked : Finset (Sym2 W), marked ⊆ J.edgeFinset ∧
      (marked.card : ℝ) ≤ 2 * p * J.edgeFinset.card ∧
        ¬F.IsContained (H.deleteEdges (marked : Set (Sym2 W))) := by
  apply exists_seed_assignment_obstruction F H J hJ hF D D hmax hhost hD hD
    s q b (3 / 4) p (by norm_num) hp₀ hp₁ (by simpa using hlog)
  exact ordinary_seed_assignment_coverage F H J hF hJ d D s q b hd hmin hmax hhost hq hsmall
    ρ α hρ hα₀ hα₁ hgap hnodense hseed hlarge

end Erdos911
