import Erdos911.SeedCounting

namespace Erdos911

abbrev SeedDescription {V W : Type*} [Fintype V]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) :=
  Σ S : {S : Finset V // S.card ≤ s ∧ (F.induce (S : Set V)).Connected},
    ((F.induce (S.val : Set V)) →g H) × Finset (S.val : Set V)

noncomputable instance seedDescriptionFintype {V W : Type*}
    [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) : Fintype (SeedDescription F H s) := by
  classical
  unfold SeedDescription
  infer_instance

def forgetSeedRoot {V W : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (H : SimpleGraph W) (root : V) (image : W) (s : ℕ)
    (c : RootedSeedConfiguration F H root image s) : SeedDescription F H s :=
  ⟨⟨c.1.val, (rooted_seed_properties F root s c.1).2⟩, c.2.1.val, c.2.2⟩

noncomputable def seedsAtVertex {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) (root : V) (image : W) :
    Finset (SeedDescription F H s) := by
  classical
  exact Finset.univ.filter (fun c => ∃ h : root ∈ c.1.val, c.2.1 ⟨root, h⟩ = image)

theorem mem_seedsAtVertex {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) (root : V) (image : W)
    (c : SeedDescription F H s) :
    c ∈ seedsAtVertex F H s root image ↔ ∃ h : root ∈ c.1.val, c.2.1 ⟨root, h⟩ = image := by
  classical
  simp only [seedsAtVertex, Finset.mem_filter, Finset.mem_univ, true_and]

theorem seedsAtVertex_card_le {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (F : SimpleGraph V) [DecidableRel F.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (Δ D : ℕ)
    (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (root : V) (image : W) (s : ℕ) :
    (seedsAtVertex F H s root image).card ≤
      (s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s := by
  classical
  have hsub : seedsAtVertex F H s root image ⊆
      Finset.univ.image (forgetSeedRoot F H root image s) := by
    intro c hc
    obtain ⟨hroot, himage⟩ := (mem_seedsAtVertex F H s root image c).mp hc
    let S : rootedConnectedSetsAtMost F root s := ⟨c.1.val, by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hroot, c.1.property⟩⟩
    let r : RootedSeedConfiguration F H root image s :=
      ⟨S, ⟨c.2.1, himage⟩, c.2.2⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  calc
    _ ≤ (Finset.univ.image (forgetSeedRoot F H root image s)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (RootedSeedConfiguration F H root image s)).card :=
      Finset.card_image_le
    _ = Fintype.card (RootedSeedConfiguration F H root image s) := Finset.card_univ
    _ ≤ _ := rooted_seed_configuration_count F H Δ D hΔ hD hΔpos hDpos root image s

noncomputable def seedsMeetingAnchors {V W : Type*}
    [Fintype V] [Fintype W]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) (A : Finset W) :
    Finset (SeedDescription F H s) := by
  classical
  exact Finset.univ.biUnion (fun root => A.biUnion (seedsAtVertex F H s root))

theorem mem_seedsMeetingAnchors {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) (H : SimpleGraph W) (s : ℕ) (A : Finset W)
    (c : SeedDescription F H s) :
    c ∈ seedsMeetingAnchors F H s A ↔
      ∃ v : (c.1.val : Set V), c.2.1 v ∈ A := by
  classical
  simp only [seedsMeetingAnchors, Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_seedsAtVertex]
  constructor
  · rintro ⟨root, image, hA, hroot, himage⟩
    exact ⟨⟨root, hroot⟩, himage ▸ hA⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.val, c.2.1 v, hv, v.property, rfl⟩

theorem seedsMeetingAnchors_card_le {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (Δ D : ℕ) (hΔ : ∀ v, F.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (s : ℕ) (A : Finset W) :
    (seedsMeetingAnchors F H s A).card ≤
      Fintype.card V * A.card * ((s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s) := by
  classical
  have hdef : seedsMeetingAnchors F H s A =
      (Finset.univ : Finset V).biUnion (fun root => A.biUnion (seedsAtVertex F H s root)) := by
    ext c
    rw [mem_seedsMeetingAnchors]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_seedsAtVertex]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v.val, c.2.1 v, hv, v.property, rfl⟩
    · rintro ⟨v, w, hw, hv, hmap⟩
      exact ⟨⟨v, hv⟩, hmap ▸ hw⟩
  rw [hdef]
  calc
    _ ≤ ∑ root : V, (A.biUnion (seedsAtVertex F H s root)).card := Finset.card_biUnion_le
    _ ≤ ∑ root : V, ∑ image ∈ A, (seedsAtVertex F H s root image).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ _root : V, ∑ _image ∈ A, (s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s := by
      apply Finset.sum_le_sum
      intro root _
      exact Finset.sum_le_sum (fun image _ =>
        seedsAtVertex_card_le F H Δ D hΔ hD hΔpos hDpos root image s)
    _ = _ := by simp [Nat.mul_assoc]

end Erdos911
