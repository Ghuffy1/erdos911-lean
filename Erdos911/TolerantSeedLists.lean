import Erdos911.SampledOrdinaryAssignments
import Erdos911.RetentionDefects
import Erdos911.TupleNeighborCoverage

namespace Erdos911

def seedMapAgrees {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ)
    (c : SeedDescription F H s) (f : V → W) : Prop :=
  ∀ u : (c.1.val : Set V), c.2.1 u = f u.val

noncomputable def unseededCandidateList {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ)
    (c : SeedDescription F H s) (v : V) : Finset W := by
  classical
  exact if v ∈ c.1.val then ∅ else seedCandidateList F H J s τ c v

theorem mem_unseededCandidateList {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ)
    (c : SeedDescription F H s) (v : V) (w : W) :
    w ∈ unseededCandidateList F H J s τ c v ↔
      v ∉ c.1.val ∧ w ∈ seedCandidateList F H J s τ c v := by
  classical
  by_cases hv : v ∈ c.1.val <;> simp [unseededCandidateList, hv]

theorem unseededCandidateList_subset {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ)
    (c : SeedDescription F H s) (v : V) :
    unseededCandidateList F H J s τ c v ⊆ seedCandidateList F H J s τ c v := by
  intro w hw
  exact ((mem_unseededCandidateList F H J s τ c v w).mp hw).2

theorem candidateSlice_eq_slotGoodNeighbors {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W) [DecidableRel J.Adj]
    (f : F.Copy H) (v : Fin n) (w : W) :
    candidateSlice (F.neighborFinset v) (fun u => J.neighborFinset (f u)) w =
      slotGoodNeighbors F J f v (some w) := by
  classical
  ext u
  simp only [candidateSlice, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
    mem_slotGoodNeighbors, Option.some.injEq, forall_eq', J.adj_comm]

/-- A connected sampled seed produces dense candidate lists at tolerance
`epsilon`, containing the true images of all sufficiently retained roles. -/
theorem exists_tolerant_seed_lists_agree {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hF : F.Connected) (hJ : J ≤ H) (f : F.Copy H) (d D s q : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hq : 2 ≤ q) (hsmall : 2 * q ≤ d)
    (ρ α ε : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 5)
    (hgap : ρ * d + q < (1 - 5 * ε) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-(ε ^ 2 * (α * d)) / 128)) ≤ s) :
    ∃ c : SeedDescription F H s,
      seedMapAgrees F H s c f ∧
      (∀ v, (unseededCandidateList F H J s (1 - 4 * ε) c v).card ≤ q) ∧
      (∀ v w, w ∈ unseededCandidateList F H J s (1 - 4 * ε) c v →
        (1 - 5 * ε) * F.degree v ≤ ((slotGoodNeighbors F J f v (some w)).card : ℝ)) ∧
      (∀ v, v ∉ c.1.val → v ∉ retentionDefects F (copyRetainedGraph J f) ε →
        f v ∈ unseededCandidateList F H J s (1 - 4 * ε) c v) := by
  classical
  let N := fun u => J.neighborFinset (f u)
  have hN : ∀ u, (N u).card ≤ D := by
    intro u
    exact ((SimpleGraph.Copy.ofLE J H hJ).degree_le (f u)).trans (hhost (f u))
  obtain ⟨ω, S, hflags, hconn, haccurate, hsize⟩ := exists_accurate_connected_seed F hF N d D
    hd hmin hmax hN α ε hα₀ hα₁ hε₀ (by linarith)
  have hScard : S.card ≤ s := by exact_mod_cast hsize.trans hseed
  let c := seedDescriptionOfCopy f S s hScard hconn ω
  have hcounts (v : Fin n) (w : W) :
      ((seedFlagNeighbors F H s c v).card : ℝ) = sampleCount (F.neighborFinset v) ω ∧
      ((seedHitNeighbors F H J s c v w).card : ℝ) = sampleCount (candidateSlice (F.neighborFinset v) N w) ω :=
    ⟨copy_seed_flag_count f S s hScard hconn ω hflags v,
      copy_seed_hit_count J f S s hScard hconn ω hflags v w⟩
  have hacc : ∀ v, v ∉ S → ∀ w,
      |((seedHitNeighbors F H J s c v w).card : ℝ) / (seedFlagNeighbors F H s c v).card -
        ((slotGoodNeighbors F J f v (some w)).card : ℝ) / F.degree v| ≤ ε := by
    intro v hv w
    rw [(hcounts v w).1, (hcounts v w).2]
    rw [← candidateSlice_eq_slotGoodNeighbors F H J f v w]
    exact (haccurate v hv).2 w
  have hlistBound : ∀ v, (seedCandidateList F H J s (1 - 4 * ε) c v).card < q := by
    apply seedCandidateList_card_lt F H J s (1 - 4 * ε) ε ρ c
      (fun v => (F.neighborFinset v).image f) q hq hρ hnodense
    · intro v _
      rw [copy_neighbor_images_card]
      exact hsmall.trans (hmin v)
    · intro v _
      rw [copy_neighbor_images_card]
      have hdeg : (d : ℝ) ≤ F.degree v := by exact_mod_cast hmin v
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      have hcoefficient : 0 ≤ 1 - 5 * ε - ρ := by
        nlinarith only [hgap, Nat.cast_nonneg (α := ℝ) q, hdpos]
      have hscale := mul_le_mul_of_nonneg_left hdeg hcoefficient
      nlinarith only [hscale, hgap]
    · intro v hv w
      have h := hacc v hv w
      rw [← candidateSlice_eq_slotGoodNeighbors F H J f v w, copy_candidateSlice_card] at h
      simpa only [copy_neighbor_images_card] using h
  refine ⟨c, (by intro u; rfl), ?_, ?_, ?_⟩
  · intro v
    exact (Finset.card_le_card (unseededCandidateList_subset F H J s (1 - 4 * ε) c v)).trans
      (hlistBound v).le
  · intro v w hw
    obtain ⟨hv, hw⟩ := (mem_unseededCandidateList F H J s (1 - 4 * ε) c v w).mp hw
    rcases (mem_seedCandidateList F H J s (1 - 4 * ε) c v w).mp hw with hseedImage | hscore
    · obtain ⟨u, huv, _⟩ := hseedImage
      exact (hv (huv ▸ u.property)).elim
    · have hdenpos : (0 : ℝ) < (seedFlagNeighbors F H s c v).card := by exact_mod_cast hscore.2.1
      have hscore' := (le_div_iff₀ hdenpos).mpr hscore.2.2
      have haccuracy := hacc v hv w
      have hdegreepos : (0 : ℝ) < F.degree v := by exact_mod_cast hd.trans_le (hmin v)
      apply (le_div_iff₀ hdegreepos).mp
      linarith [(abs_le.mp haccuracy).2]
  · intro v hv hret
    have hpositive := (haccurate v hv).1
    rw [← (hcounts v (f v)).1] at hpositive
    have hdegreepos : (0 : ℝ) < F.degree v := by exact_mod_cast hd.trans_le (hmin v)
    have hretained := retentionDefects_retained_degree F (copyRetainedGraph J f) ε v hret
    have hfraction := (le_div_iff₀ hdegreepos).mpr hretained
    have haccuracy := hacc v hv (f v)
    rw [← candidateSlice_eq_slotGoodNeighbors F H J f v (f v), copy_self_candidateSlice_card] at haccuracy
    apply (mem_unseededCandidateList F H J s (1 - 4 * ε) c v (f v)).mpr
    refine ⟨hv, (mem_seedCandidateList F H J s (1 - 4 * ε) c v (f v)).mpr (Or.inr ⟨hv, ?_, ?_⟩)⟩
    · exact_mod_cast hpositive
    · apply (le_div_iff₀ hpositive).mp
      linarith [(abs_le.mp haccuracy).1]

theorem exists_tolerant_seed_lists {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hF : F.Connected) (hJ : J ≤ H) (f : F.Copy H) (d D s q : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hhost : ∀ w, H.degree w ≤ D) (hq : 2 ≤ q) (hsmall : 2 * q ≤ d)
    (ρ α ε : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 5)
    (hgap : ρ * d + q < (1 - 5 * ε) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (hseed : 3 * n * (α + (4 * (D * D : ℕ) + 1 : ℝ) *
      Real.exp (-(ε ^ 2 * (α * d)) / 128)) ≤ s) :
    ∃ c : SeedDescription F H s,
      (∀ v, (unseededCandidateList F H J s (1 - 4 * ε) c v).card ≤ q) ∧
      (∀ v w, w ∈ unseededCandidateList F H J s (1 - 4 * ε) c v →
        (1 - 5 * ε) * F.degree v ≤ ((slotGoodNeighbors F J f v (some w)).card : ℝ)) ∧
      (∀ v, v ∉ c.1.val → v ∉ retentionDefects F (copyRetainedGraph J f) ε →
        f v ∈ unseededCandidateList F H J s (1 - 4 * ε) c v) := by
  obtain ⟨c, _, hlist, hdense, htrue⟩ := exists_tolerant_seed_lists_agree F H J hF hJ f d D s q
    hd hmin hmax hhost hq hsmall ρ α ε hρ hα₀ hα₁ hε₀ hε₁ hgap hnodense hseed
  exact ⟨c, hlist, hdense, htrue⟩

end Erdos911
