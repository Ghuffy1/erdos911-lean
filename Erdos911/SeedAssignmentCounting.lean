import Erdos911.SeedCandidateLists
import Erdos911.CopyImages

namespace Erdos911

noncomputable def partialListAssignments {V W : Type*} [Fintype V]
    (L : V → Finset W) : Finset (V → Option W) := by
  classical
  exact Fintype.piFinset (fun v => insert none ((L v).image some))

theorem mem_partialListAssignments {V W : Type*} [Fintype V]
    (L : V → Finset W) (a : V → Option W) :
    a ∈ partialListAssignments L ↔ ∀ v w, a v = some w → w ∈ L v := by
  classical
  constructor
  · intro ha v w hv
    have h := Fintype.mem_piFinset.mp ha v
    rcases Finset.mem_insert.mp h with hnone | hsome
    · rw [hv] at hnone
      cases hnone
    · obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp hsome
      have heq : z = w := Option.some.inj (hzw.trans hv)
      exact heq ▸ hz
  · intro ha
    apply Fintype.mem_piFinset.mpr
    intro v
    cases h : a v with
    | none => exact Finset.mem_insert_self _ _
    | some w => exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, ha v w h, rfl⟩)

theorem partialListAssignments_card_le {V W : Type*} [Fintype V]
    (L : V → Finset W) (q : ℕ) (hq : ∀ v, (L v).card ≤ q) :
    (partialListAssignments L).card ≤ (q + 1) ^ Fintype.card V := by
  classical
  unfold partialListAssignments
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _v : V, (q + 1) := by
      apply Finset.prod_le_prod
      intro v _
      exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (Finset.card_image_le.trans (hq v)) 1)
    _ = _ := by simp

noncomputable def partialAssignmentEdges {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (J : SimpleGraph W) (a : V → Option W) : Finset J.edgeSet := by
  classical
  exact Finset.univ.filter (fun e => ∃ u v, F.Adj u v ∧
    a u = some e.val.out.1 ∧ a v = some e.val.out.2)

theorem mem_partialAssignmentEdges {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (J : SimpleGraph W) (a : V → Option W) (e : J.edgeSet) :
    e ∈ partialAssignmentEdges F J a ↔ ∃ u v, F.Adj u v ∧
      a u = some e.val.out.1 ∧ a v = some e.val.out.2 := by
  classical
  simp only [partialAssignmentEdges, Finset.mem_filter, Finset.mem_univ, true_and]

theorem partialAssignmentEdges_of_adj {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (J : SimpleGraph W) (a : V → Option W)
    (u v : V) (w z : W) (huv : F.Adj u v) (hwz : J.Adj w z)
    (hu : a u = some w) (hv : a v = some z) :
    (⟨s(w, z), hwz⟩ : J.edgeSet) ∈ partialAssignmentEdges F J a := by
  let e : J.edgeSet := ⟨s(w, z), hwz⟩
  apply (mem_partialAssignmentEdges F J a e).mpr
  rcases Sym2.eq_iff.mp e.val.out_eq with h | h
  · exact ⟨u, v, huv, hu.trans (congrArg some h.1.symm), hv.trans (congrArg some h.2.symm)⟩
  · exact ⟨v, u, huv.symm, hv.trans (congrArg some h.1.symm), hu.trans (congrArg some h.2.symm)⟩

def PartialAssignmentAgrees {V W : Type*} (a : V → Option W) (f : V → W) : Prop :=
  ∀ v w, a v = some w → f v = w

theorem partialAssignmentEdges_subset_copy {V W : Type*} [Fintype V] [Fintype W]
    {F : SimpleGraph V} {H : SimpleGraph W} (J : SimpleGraph W)
    (a : V → Option W) (f : F.Copy H) (h : PartialAssignmentAgrees a f) :
    ∀ e ∈ partialAssignmentEdges F J a, e.val ∈ copyRawEdges f := by
  intro e he
  obtain ⟨u, v, huv, hu, hv⟩ := (mem_partialAssignmentEdges F J a e).mp he
  apply (mem_copyRawEdges_iff_exists f e.val).mpr
  refine ⟨⟨s(u, v), huv⟩, ?_⟩
  have hfu := h u e.val.out.1 hu
  have hfv := h v e.val.out.2 hv
  change s(f u, f v) = e.val
  rw [hfu, hfv]
  exact e.val.out_eq

noncomputable def boundedSeedDescriptions {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q : ℕ) :
    Finset (SeedDescription F H s) := by
  classical
  exact Finset.univ.filter (fun c => ∀ v, (seedCandidateList F H J s τ c v).card ≤ q)

theorem mem_boundedSeedDescriptions {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q : ℕ)
    (c : SeedDescription F H s) :
    c ∈ boundedSeedDescriptions F H J s τ q ↔
      ∀ v, (seedCandidateList F H J s τ c v).card ≤ q := by
  classical
  simp only [boundedSeedDescriptions, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev SeedAssignment {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H J : SimpleGraph W) (s : ℕ) (τ : ℝ) (q : ℕ) :=
  Σ c : boundedSeedDescriptions F H J s τ q,
    partialListAssignments (seedCandidateList F H J s τ c.val)

theorem SeedAssignment.ext {V W : Type*} [Fintype V] [Fintype W]
    {F : SimpleGraph V} {H J : SimpleGraph W} {s q : ℕ} {τ : ℝ}
    (a b : SeedAssignment F H J s τ q)
    (hseed : a.1.val = b.1.val) (hvalues : a.2.val = b.2.val) : a = b := by
  rcases a with ⟨c, a⟩
  rcases b with ⟨d, b⟩
  have hcd : c = d := Subtype.ext hseed
  subst d
  have hab : a = b := Subtype.ext hvalues
  subst b
  rfl

/-- The edge of a partial assignment anchors a bounded seed in one host
neighborhood. Unspecified roles contribute one extra choice per list. -/
theorem seed_assignment_edge_incidence {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel J.Adj] (hJ : J ≤ H)
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s q : ℕ) (τ : ℝ) (hτ : 0 < τ) (e : J.edgeSet) :
    ((Finset.univ : Finset (SeedAssignment F H J s τ q)).filter
      (fun a => e ∈ partialAssignmentEdges F J a.2.val)).card ≤
        (Fintype.card V * (D + 1) *
          ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s)) * (q + 1) ^ Fintype.card V := by
  classical
  let I := (Finset.univ : Finset (SeedAssignment F H J s τ q)).filter
    (fun a => e ∈ partialAssignmentEdges F J a.2.val)
  let C := boundedSeedDescriptions F H J s τ q ∩ seedsWithCandidate F H J s τ e.val.out.1
  have hseed : ∀ a : I, a.val.1.val ∈ C := by
    intro a
    apply Finset.mem_inter.mpr
    refine ⟨a.val.1.property, ?_⟩
    obtain ⟨u, v, _, hu, _⟩ := (mem_partialAssignmentEdges F J a.val.2.val e).mp
      (Finset.mem_filter.mp a.property).2
    apply (mem_seedsWithCandidate F H J s τ e.val.out.1 a.val.1.val).mpr
    exact ⟨u, (mem_partialListAssignments _ a.val.2.val).mp a.val.2.property u e.val.out.1 hu⟩
  let encode : I → (Σ c : C, partialListAssignments (seedCandidateList F H J s τ c.val)) :=
    fun a => ⟨⟨a.val.1.val, hseed a⟩, a.val.2⟩
  have hinj : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply SeedAssignment.ext
    · exact congrArg (fun z : Σ c : C, partialListAssignments (seedCandidateList F H J s τ c.val) =>
        z.1.val) hab
    · exact congrArg (fun z : Σ c : C, partialListAssignments (seedCandidateList F H J s τ c.val) =>
        z.2.val) hab
  have hfibers : ∀ c : C, (partialListAssignments (seedCandidateList F H J s τ c.val)).card ≤
      (q + 1) ^ Fintype.card V := by
    intro c
    exact partialListAssignments_card_le _ q
      ((mem_boundedSeedDescriptions F H J s τ q c.val).mp (Finset.mem_inter.mp c.property).1)
  calc
    I.card = Fintype.card I := (Fintype.card_coe I).symm
    _ ≤ Fintype.card (Σ c : C, partialListAssignments (seedCandidateList F H J s τ c.val)) :=
      Fintype.card_le_of_injective encode hinj
    _ = ∑ c : C, (partialListAssignments (seedCandidateList F H J s τ c.val)).card := by
      simp only [Fintype.card_sigma, Fintype.card_coe]
    _ ≤ ∑ _c : C, (q + 1) ^ Fintype.card V := Finset.sum_le_sum (fun c _ => hfibers c)
    _ = C.card * (q + 1) ^ Fintype.card V := by simp
    _ ≤ (seedsWithCandidate F H J s τ e.val.out.1).card * (q + 1) ^ Fintype.card V :=
      Nat.mul_le_mul_right _ (Finset.card_le_card Finset.inter_subset_right)
    _ ≤ _ := Nat.mul_le_mul_right _
      (seedsWithCandidate_card_le F H J hJ Δ D hΔ hD hΔpos hDpos s τ hτ e.val.out.1)

end Erdos911
