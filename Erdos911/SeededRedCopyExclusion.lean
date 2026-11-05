import Erdos911.CopyCandidateMatching
import Erdos911.MarkedNeighborhoodStars

namespace Erdos911

theorem unseeded_candidate_has_flagged_neighbor {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) [DecidableRel J.Adj]
    (s : ℕ) (τ : ℝ) (hτ : 0 < τ) (c : SeedDescription F H s)
    (v : V) (w : W) (hw : w ∈ unseededCandidateList F H J s τ c v) :
    ∃ u : (c.1.val : Set V), F.Adj v u.val ∧ J.Adj w (c.2.1 u) := by
  classical
  obtain ⟨hv, hw⟩ := (mem_unseededCandidateList F H J s τ c v w).mp hw
  rcases (mem_seedCandidateList F H J s τ c v w).mp hw with ⟨u, huv, _⟩ | ⟨_, hflag, hhit⟩
  · exact (hv (huv ▸ u.property)).elim
  · have hflagR : (0 : ℝ) < (seedFlagNeighbors F H s c v).card := by exact_mod_cast hflag
    have hhitpos : 0 < (seedHitNeighbors F H J s c v w).card := by
      exact_mod_cast (mul_pos hτ hflagR).trans_le hhit
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hhitpos
    obtain ⟨huflag, huJ⟩ := (mem_seedHitNeighbors F H J s c v w u).mp hu
    exact ⟨u, (Finset.mem_filter.mp huflag).2, huJ⟩

/-- A marked true image with a flagged seed neighbor would supply an edge
of the copy in the deleted star set. -/
theorem seeded_copy_candidate_unmarked {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : F.Copy H) (s : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (c : SeedDescription F H s)
    (S : Finset W) (havoid : Disjoint (copyRawEdges f) (incidentEdgesAtSet H S))
    (v : V) (hv : f v ∈ unseededCandidateList F H J s τ c v) : f v ∉ S := by
  intro hmarked
  obtain ⟨u, huv, _⟩ := unseeded_candidate_has_flagged_neighbor F H J s τ hτ c v (f v) hv
  have hecopy : s(f v, f u.val) ∈ copyRawEdges f := by
    apply (mem_copyRawEdges_iff_exists f _).mpr
    exact ⟨⟨s(v, u.val), huv⟩, rfl⟩
  have hestar : s(f v, f u.val) ∈ incidentEdgesAtSet H S :=
    adjacent_marked_edge H S (f v) (f u.val) (map_rel f.toHom huv) hmarked
  exact Finset.disjoint_left.mp havoid hecopy hestar

theorem blocked_seed_roles_exceptional {V W I K : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype I] [Fintype K]
    (F : SimpleGraph V) (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : F.Copy H) (s : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (c : SeedDescription F H s)
    (B : I → Finset W) (h : ℕ) (marks : (Fin h × I) → Bool)
    (havoid : Disjoint (copyRawEdges f) (incidentEdgesAtSet H (roundMarkedVertices B h marks)))
    (E : Finset V) (htrue : ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v)
    (role : K → V) (k : K)
    (hk : marks ∈ listBlocked B h (unseededCandidateList F H J s τ c (role k))) :
    role k ∈ E := by
  by_contra hnot
  have hmem := htrue (role k) hnot
  have hmarked := (listBlocked_iff_subset_roundMarked B h _ marks).mp hk hmem
  exact seeded_copy_candidate_unmarked F H J f s τ hτ c _ havoid (role k) hmem hmarked

/-- Every blocked list of a surviving copy is charged to a distinct
exceptional target role. -/
theorem seeded_copy_few_blocked {V W I K : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype I] [Fintype K]
    (F : SimpleGraph V) (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj]
    (f : F.Copy H) (s : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (c : SeedDescription F H s)
    (B : I → Finset W) (h : ℕ) (marks : (Fin h × I) → Bool)
    (havoid : Disjoint (copyRawEdges f) (incidentEdgesAtSet H (roundMarkedVertices B h marks)))
    (E : Finset V) (htrue : ∀ v, v ∉ E → f v ∈ unseededCandidateList F H J s τ c v)
    (role : K → V) (hrole : Function.Injective role) :
    (∑ k, (listBlocked B h (unseededCandidateList F H J s τ c (role k))).indicator
      (fun _ => (1 : ℝ)) marks) ≤ E.card := by
  classical
  let A := Finset.univ.filter (fun k =>
    marks ∈ listBlocked B h (unseededCandidateList F H J s τ c (role k)))
  have hsub : A.image role ⊆ E := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact blocked_seed_roles_exceptional F H J f s τ hτ c B h marks havoid E htrue
      role k (Finset.mem_filter.mp hk).2
  have hcard : A.card ≤ E.card := by
    rw [← Finset.card_image_of_injective A hrole]
    exact Finset.card_le_card hsub
  have hsum : (∑ k, (listBlocked B h (unseededCandidateList F H J s τ c (role k))).indicator
      (fun _ => (1 : ℝ)) marks) = A.card := by
    simp only [Set.indicator, A, Finset.sum_boole]
  exact hsum.trans_le (by exact_mod_cast hcard)

end Erdos911
