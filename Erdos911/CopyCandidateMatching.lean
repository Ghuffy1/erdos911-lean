import Erdos911.ThickCandidateLists
import Erdos911.TolerantSeedLists

namespace Erdos911

theorem thick_candidate_neighbor_degree {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (J : SimpleGraph W) [DecidableRel J.Adj]
    (L : V → Finset W) (s : ℕ) (T : ℝ) (hs : 1 ≤ s)
    (v : thickCandidateRoles J L s T) (w : W) (hw : w ∈ L v.val) : T ≤ (J.degree w : ℝ) := by
  have h := thickCandidateRoles_common J L s T hs v {w}
    (Finset.singleton_subset_iff.mpr hw) (by simpa only [Finset.card_singleton] using hs)
  have heq : commonCenters J.Adj {w} = J.neighborFinset w := by
    classical
    ext z
    simp only [mem_commonCenters_iff, Finset.mem_singleton, forall_eq, SimpleGraph.mem_neighborFinset]
  simpa only [heq, J.card_neighborFinset_eq_degree] using h

/-- A surviving copy and a small exceptional set certify that the
canonical matching retains at least the target edge count divided by Delta. -/
theorem copy_thick_matching_mass {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hJ : J ≤ H) (f : G.Copy H) (L : V → Finset W) (s Δ P : ℕ) (T ε : ℝ) (S : Finset V)
    (hP : 0 < P) (hT : 0 < T) (hTP : T < P)
    (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (hbudget : (s : ℝ) * ε ≤ 1 / 2)
    (hdegree : ∀ v, 0 < G.degree v) (hΔ : ∀ v, G.degree v ≤ Δ)
    (hdense : ∀ v w, w ∈ L v → (1 - ε) * G.degree v ≤
      ((slotGoodNeighbors G J f v (some w)).card : ℝ))
    (htrue : ∀ v, v ∉ S → f v ∈ L v)
    (hgood : ¬IsStarDeficitImage H J (copyVertices f) (copyRawEdges f) s P
      ((G.edgeSet.ncard : ℝ) / 32 * Real.log ((P : ℝ) / T)))
    (hcost : 2 * (Δ : ℝ) * S.card ≤ (G.edgeSet.ncard : ℝ) / 2) :
    (G.edgeSet.ncard : ℝ) ≤ (Δ : ℝ) * (matchedRoles
      (maximumListMatching (fun v : thickCandidateRoles J L s T => L v.val))).card := by
  have hbad := small_common_roles_degree_bound G H J hJ f L s P T ε
    hP hT hTP hε₀ hε₁ hbudget hdegree hdense hgood
  have hcoverNat := thick_matching_degree_cover G J L s Δ T f f.injective S hΔ htrue
  rw [G.edgeFinset_card, Set.fintypeCard_eq_ncard] at hcoverNat
  have hcover : 2 * (G.edgeSet.ncard : ℝ) ≤
      (Δ : ℝ) * (matchedRoles (maximumListMatching
        (fun v : thickCandidateRoles J L s T => L v.val))).card +
      (∑ v ∈ smallCommonNeighborhoodRoles J L s T, (G.degree v : ℝ)) + 2 * Δ * S.card := by
    exact_mod_cast hcoverNat
  have he : (0 : ℝ) ≤ G.edgeSet.ncard := Nat.cast_nonneg _
  nlinarith only [hcover, hbad, hcost, he]

theorem seed_retention_exception_card {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H)
    (d s : ℕ) (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (ε : ℝ) (hε : 0 < ε)
    (c : SeedDescription F H s) :
    ((c.1.val ∪ retentionDefects F (copyRetainedGraph J f) ε).card : ℝ) ≤
      s + (F \ copyRetainedGraph J f).edgeSet.ncard / (ε * d) := by
  have hdefect := retentionDefects_card_bound F (copyRetainedGraph J f)
    (copyRetainedGraph_le J f) d hmin ε hε.le
  have hden : (0 : ℝ) < ε * d := mul_pos hε (by exact_mod_cast hd)
  have hdefect' : ((retentionDefects F (copyRetainedGraph J f) ε).card : ℝ) ≤
      (F \ copyRetainedGraph J f).edgeSet.ncard / (ε * d) := by
    apply (le_div_iff₀ hden).mpr
    simpa only [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard, mul_assoc, mul_comm,
      mul_left_comm] using hdefect
  have hseed : (c.1.val.card : ℝ) ≤ s := by exact_mod_cast c.1.property.1
  have hcard : ((c.1.val ∪ retentionDefects F (copyRetainedGraph J f) ε).card : ℝ) ≤
      c.1.val.card + (retentionDefects F (copyRetainedGraph J f) ε).card := by
    exact_mod_cast Finset.card_union_le c.1.val (retentionDefects F (copyRetainedGraph J f) ε)
  linarith

/-- The sampled lists of an actual surviving copy contain a large
matching, chosen solely from the seed and its candidate lists. -/
theorem exists_tolerant_seed_matching_agree {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hF : F.Connected) (hJ : J ≤ H) (f : F.Copy H) (d D Δ s q r P : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hΔ : ∀ v, F.degree v ≤ Δ) (hhost : ∀ w, H.degree w ≤ D)
    (hq : 2 ≤ q) (hsmall : 2 * q ≤ d) (hP : 0 < P)
    (ρ α ε T : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
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
      (F.edgeSet.ncard : ℝ) / 2) :
    ∃ c : SeedDescription F H s,
      seedMapAgrees F H s c f ∧
      let L := unseededCandidateList F H J s (1 - 4 * ε) c
      let S := c.1.val ∪ retentionDefects F (copyRetainedGraph J f) ε
      (∀ v, (L v).card ≤ q) ∧
      (F.edgeSet.ncard : ℝ) ≤ (Δ : ℝ) * (matchedRoles
        (maximumListMatching (fun v : thickCandidateRoles J L r T => L v.val))).card ∧
      (∀ v, v ∉ S → f v ∈ L v) ∧
      (S.card : ℝ) ≤ s + (F \ copyRetainedGraph J f).edgeSet.ncard / (ε * d) := by
  classical
  obtain ⟨c, hagree, hlist, hdense, htrue⟩ := exists_tolerant_seed_lists_agree F H J hF hJ f d D s q
    hd hmin hmax hhost hq hsmall ρ α ε hρ hα₀ hα₁ hε₀.le hε₁ hgap hnodense hseed
  let L := unseededCandidateList F H J s (1 - 4 * ε) c
  let S := c.1.val ∪ retentionDefects F (copyRetainedGraph J f) ε
  have htrue' : ∀ v, v ∉ S → f v ∈ L v := by
    intro v hv
    apply htrue v
    · exact fun h => hv (Finset.mem_union_left _ h)
    · exact fun h => hv (Finset.mem_union_right _ h)
  have hScard := seed_retention_exception_card F H J f d s hd hmin ε hε₀ c
  have hcost' : 2 * (Δ : ℝ) * S.card ≤ (F.edgeSet.ncard : ℝ) / 2 :=
    (mul_le_mul_of_nonneg_left hScard (by positivity)).trans hcost
  have hmass := copy_thick_matching_mass F H J hJ f L r Δ P T (5 * ε) S
    hP hT hTP (by positivity) (by linarith) htuple
    (fun v => hd.trans_le (hmin v)) hΔ hdense htrue' hgood hcost'
  exact ⟨c, hagree, hlist, hmass, htrue', hScard⟩

theorem exists_tolerant_seed_matching {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (H J : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel J.Adj]
    (hF : F.Connected) (hJ : J ≤ H) (f : F.Copy H) (d D Δ s q r P : ℕ)
    (hd : 0 < d) (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hΔ : ∀ v, F.degree v ≤ Δ) (hhost : ∀ w, H.degree w ≤ D)
    (hq : 2 ≤ q) (hsmall : 2 * q ≤ d) (hP : 0 < P)
    (ρ α ε T : ℝ) (hρ : 0 ≤ ρ) (hα₀ : 0 < α) (hα₁ : α ≤ 1)
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
      (F.edgeSet.ncard : ℝ) / 2) :
    ∃ c : SeedDescription F H s,
      let L := unseededCandidateList F H J s (1 - 4 * ε) c
      let S := c.1.val ∪ retentionDefects F (copyRetainedGraph J f) ε
      (∀ v, (L v).card ≤ q) ∧
      (F.edgeSet.ncard : ℝ) ≤ (Δ : ℝ) * (matchedRoles
        (maximumListMatching (fun v : thickCandidateRoles J L r T => L v.val))).card ∧
      (∀ v, v ∉ S → f v ∈ L v) ∧
      (S.card : ℝ) ≤ s + (F \ copyRetainedGraph J f).edgeSet.ncard / (ε * d) := by
  obtain ⟨c, _, hlist, hmass, htrue, hScard⟩ := exists_tolerant_seed_matching_agree F H J hF hJ f
    d D Δ s q r P hd hmin hmax hΔ hhost hq hsmall hP ρ α ε T hρ hα₀ hα₁ hε₀ hε₁ hT hTP
    hgap hnodense hseed htuple hgood hcost
  exact ⟨c, hlist, hmass, htrue, hScard⟩

end Erdos911
