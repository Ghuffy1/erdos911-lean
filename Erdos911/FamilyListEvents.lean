import Erdos911.BlockedListEvents
import Erdos911.TolerantSeedLists

namespace Erdos911

noncomputable def familyListCoordinates {V I W : Type*}
    [Fintype V] [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : V → Finset W) : Finset (Fin h × I) := by
  classical
  exact Finset.univ.biUnion (fun v => listBlockCoordinates B h (L v))

theorem mem_familyListCoordinates {V I W : Type*}
    [Fintype V] [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : V → Finset W) (x : Fin h × I) :
    x ∈ familyListCoordinates B h L ↔ ∃ v, ¬Disjoint (B x.2) (L v) := by
  classical
  simp only [familyListCoordinates, Finset.mem_biUnion, Finset.mem_univ, true_and,
    listBlockCoordinates, Finset.mem_filter]

theorem listBlockCoordinates_card_le {I W : Type*} [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : Finset W) (N : ℕ)
    (hN : ∀ w ∈ L, (Finset.univ.filter (fun i => w ∈ B i)).card ≤ N) :
    (listBlockCoordinates B h L).card ≤ h * L.card * N := by
  classical
  let A := Finset.univ.filter (fun i => ¬Disjoint (B i) L)
  have hproduct : listBlockCoordinates B h L = (Finset.univ : Finset (Fin h)) ×ˢ A := by
    ext x
    simp only [listBlockCoordinates, A, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product]
  have hsub : A ⊆ L.biUnion (fun w => Finset.univ.filter (fun i => w ∈ B i)) := by
    intro i hi
    obtain ⟨w, hwB, hwL⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
    exact Finset.mem_biUnion.mpr ⟨w, hwL, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwB⟩⟩
  have hcard : A.card ≤ L.card * N := calc
    _ ≤ (L.biUnion (fun w => Finset.univ.filter (fun i => w ∈ B i))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ w ∈ L, (Finset.univ.filter (fun i => w ∈ B i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ L, N := Finset.sum_le_sum (fun w hw => hN w hw)
    _ = L.card * N := by simp
  rw [hproduct, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left h hcard

theorem familyListCoordinates_card_le {V I W : Type*}
    [Fintype V] [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : V → Finset W) (q N : ℕ)
    (hL : ∀ v, (L v).card ≤ q)
    (hN : ∀ v w, w ∈ L v → (Finset.univ.filter (fun i => w ∈ B i)).card ≤ N) :
    (familyListCoordinates B h L).card ≤ h * Fintype.card V * q * N := by
  classical
  calc
    _ ≤ ∑ v : V, (listBlockCoordinates B h (L v)).card := Finset.card_biUnion_le
    _ ≤ ∑ v : V, h * q * N := Finset.sum_le_sum (fun v _ =>
      (listBlockCoordinates_card_le B h (L v) N (hN v)).trans
        (Nat.mul_le_mul_right N (Nat.mul_le_mul_left h (hL v))))
    _ = h * Fintype.card V * q * N := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
      ring

noncomputable def fewBlockedLists {K I W : Type*}
    [Fintype K] [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : K → Finset W) (u : ℝ) :
    Set ((Fin h × I) → Bool) :=
  {marks | (∑ k, (listBlocked B h (L k)).indicator (fun _ => (1 : ℝ)) marks) ≤ u}

theorem fewBlockedLists_depends {V K I W : Type*}
    [Fintype V] [Fintype K] [Fintype I] [DecidableEq W]
    (B : I → Finset W) (h : ℕ) (L : V → Finset W) (role : K → V) (u : ℝ) :
    DependsOnlyOn (fewBlockedLists B h (fun k => L (role k)) u) (familyListCoordinates B h L) := by
  classical
  intro marks marks' heq hbad
  have hlist (k : K) : marks ∈ listBlocked B h (L (role k)) ↔
      marks' ∈ listBlocked B h (L (role k)) := by
    have hdep := (listBlocked_depends B h (L (role k))).mono (show
      listBlockCoordinates B h (L (role k)) ⊆ familyListCoordinates B h L from by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨role k, Finset.mem_univ _, hx⟩)
    exact ⟨hdep marks marks' heq, hdep marks' marks (fun x hx => (heq x hx).symm)⟩
  change (∑ k, (listBlocked B h (L (role k))).indicator (fun _ => (1 : ℝ)) marks') ≤ u
  change (∑ k, (listBlocked B h (L (role k))).indicator (fun _ => (1 : ℝ)) marks) ≤ u at hbad
  simpa only [Set.indicator, ← hlist] using hbad

/-- A coordinate can affect only seeds with a candidate in its vertex
block. The bound is independent of the number of host vertices. -/
theorem seed_family_coordinates_incidence {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (L : SeedDescription F H s → V → Finset W)
    (hL : ∀ c v, L c v ⊆ seedCandidateList F H J s τ c v)
    (B : I → Finset W) (h q : ℕ) (hB : ∀ i, (B i).card ≤ q) (x : Fin h × I) :
    (Finset.univ.filter (fun c => x ∈ familyListCoordinates B h (L c))).card ≤
      q * (Fintype.card V * (D + 1) * ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)) := by
  classical
  have hsub : Finset.univ.filter (fun c => x ∈ familyListCoordinates B h (L c)) ⊆
      (B x.2).biUnion (seedsWithCandidate F H J s τ) := by
    intro c hc
    obtain ⟨v, hv⟩ := (mem_familyListCoordinates B h (L c) x).mp (Finset.mem_filter.mp hc).2
    obtain ⟨w, hwB, hwL⟩ := Finset.not_disjoint_iff.mp hv
    exact Finset.mem_biUnion.mpr ⟨w, hwB,
      (mem_seedsWithCandidate F H J s τ w c).mpr ⟨v, hL c v hwL⟩⟩
  calc
    _ ≤ ((B x.2).biUnion (seedsWithCandidate F H J s τ)).card := Finset.card_le_card hsub
    _ ≤ ∑ w ∈ B x.2, (seedsWithCandidate F H J s τ w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ B x.2,
        Fintype.card V * (D + 1) * ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s) :=
      Finset.sum_le_sum (fun w _ => seedsWithCandidate_card_le F H J hJ Δ D hΔ hD hΔpos hDpos s τ hτ w)
    _ ≤ _ := by simp only [Finset.sum_const, nsmul_eq_mul]; exact Nat.mul_le_mul_right _ (hB x.2)

end Erdos911
