import Erdos911.MatchedListIncidence

namespace Erdos911

def IsListMatching {I W : Type*} (L : I → Finset W) (f : I → Option W) : Prop :=
  (∀ i w, f i = some w → w ∈ L i) ∧
    ∀ i j w, f i = some w → f j = some w → i = j

noncomputable def matchedRoles {I W : Type*} [Fintype I]
    (f : I → Option W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ w, f i = some w)

theorem mem_matchedRoles {I W : Type*} [Fintype I] (f : I → Option W) (i : I) :
    i ∈ matchedRoles f ↔ ∃ w, f i = some w := by
  classical
  simp only [matchedRoles, Finset.mem_filter, Finset.mem_univ, true_and]

theorem exists_maximum_list_matching {I W : Type*} [Fintype I] [Fintype W]
    (L : I → Finset W) :
    ∃ f : I → Option W, IsListMatching L f ∧
      ∀ g : I → Option W, IsListMatching L g → (matchedRoles g).card ≤ (matchedRoles f).card := by
  classical
  let matchings := Finset.univ.filter (IsListMatching L)
  have hempty : IsListMatching L (fun _ => none) := by
    constructor
    · intro i w h
      cases h
    · intro i j w h
      cases h
  have hnonempty : matchings.Nonempty :=
    ⟨fun _ => none, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hempty⟩⟩
  obtain ⟨f, hf, hmax⟩ := Finset.exists_max_image matchings (fun g => (matchedRoles g).card) hnonempty
  exact ⟨f, (Finset.mem_filter.mp hf).2, fun g hg =>
    hmax g (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)⟩

noncomputable def maximumListMatching {I W : Type*} [Fintype I] [Fintype W]
    (L : I → Finset W) : I → Option W :=
  (exists_maximum_list_matching L).choose

theorem maximumListMatching_spec {I W : Type*} [Fintype I] [Fintype W]
    (L : I → Finset W) :
    IsListMatching L (maximumListMatching L) ∧
      ∀ g : I → Option W, IsListMatching L g →
        (matchedRoles g).card ≤ (matchedRoles (maximumListMatching L)).card :=
  (exists_maximum_list_matching L).choose_spec

noncomputable def matchedRepresentative {I W : Type*} [Fintype I]
    (f : I → Option W) (i : matchedRoles f) : W :=
  ((mem_matchedRoles f i.val).mp i.property).choose

theorem matchedRepresentative_spec {I W : Type*} [Fintype I]
    (f : I → Option W) (i : matchedRoles f) : f i.val = some (matchedRepresentative f i) :=
  ((mem_matchedRoles f i.val).mp i.property).choose_spec

theorem matchedRepresentative_injective {I W : Type*} [Fintype I]
    (L : I → Finset W) (f : I → Option W) (hf : IsListMatching L f) :
    Function.Injective (matchedRepresentative f) := by
  intro i j hij
  apply Subtype.ext
  apply hf.2 i.val j.val (matchedRepresentative f i) (matchedRepresentative_spec f i)
  rw [hij]
  exact matchedRepresentative_spec f j

theorem matchedRepresentative_mem {I W : Type*} [Fintype I]
    (L : I → Finset W) (f : I → Option W) (hf : IsListMatching L f) (i : matchedRoles f) :
    matchedRepresentative f i ∈ L i.val :=
  hf.1 i.val (matchedRepresentative f i) (matchedRepresentative_spec f i)

/-- The maximum matching is chosen from the lists alone. Any injective
true-image assignment outside an exceptional set bounds the unmatched roles. -/
theorem maximum_list_matching_size {I W : Type*} [Fintype I] [Fintype W]
    (L : I → Finset W) (f : I → W) (hf : Function.Injective f)
    (S : Finset I) (hlist : ∀ i, i ∉ S → f i ∈ L i) :
    Fintype.card I ≤ (matchedRoles (maximumListMatching L)).card + S.card := by
  classical
  let g : I → Option W := fun i => if i ∈ S then none else some (f i)
  have hg : IsListMatching L g := by
    constructor
    · intro i w hi
      by_cases hS : i ∈ S
      · simp only [g, ite_eq_left hS, reduceCtorEq] at hi
      · have hvalue : f i = w := by simpa only [g, ite_eq_right hS, Option.some.injEq] using hi
        rw [← hvalue]
        exact hlist i hS
    · intro i j w hi hj
      have hiS : i ∉ S := by intro h; simp only [g, ite_eq_left h, reduceCtorEq] at hi
      have hjS : j ∉ S := by intro h; simp only [g, ite_eq_left h, reduceCtorEq] at hj
      have hiw : f i = w := by simpa only [g, ite_eq_right hiS, Option.some.injEq] using hi
      have hjw : f j = w := by simpa only [g, ite_eq_right hjS, Option.some.injEq] using hj
      exact hf (hiw.trans hjw.symm)
  have hroles : matchedRoles g = Finset.univ \ S := by
    ext i
    rw [mem_matchedRoles]
    by_cases hi : i ∈ S <;> simp only [g, hi, ite_true, ite_false, reduceCtorEq,
      exists_false, Option.some.injEq, exists_eq', Finset.mem_sdiff, Finset.mem_univ, true_and,
      not_true_eq_false, not_false_eq_true]
  have hsize : (matchedRoles g).card + S.card = Fintype.card I := by
    rw [hroles, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S), Finset.card_univ]
  have hmax := (maximumListMatching_spec L).2 g hg
  omega

theorem maximum_list_matching_read_bound {I W : Type*} [Fintype I] [Fintype W]
    [DecidableEq W] (Q : SimpleGraph W) [DecidableRel Q.Adj]
    (L : I → Finset W)
    (hclique : ∀ i, ∀ x ∈ L i, ∀ y ∈ L i, x ≠ y → Q.Adj x y)
    (q : ℕ) (hdegree : ∀ y, Q.degree y < q) (B : Finset W) (hB : B.card ≤ q) :
    ((Finset.univ : Finset (matchedRoles (maximumListMatching L))).filter
      (fun i => ¬Disjoint B (L i.val))).card ≤ q * q := by
  let f := maximumListMatching L
  have hf := (maximumListMatching_spec L).1
  exact matched_lists_read_bound Q (fun i : matchedRoles f => L i.val)
    (matchedRepresentative f) (matchedRepresentative_injective L f hf)
    (matchedRepresentative_mem L f hf) (fun i => hclique i.val) q hdegree B hB

end Erdos911
