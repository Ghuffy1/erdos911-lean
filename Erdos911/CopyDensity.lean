import Erdos911.DenseWitnessBound

namespace Erdos911

noncomputable def copyInduceImage {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {G : SimpleGraph W} (f : F.Copy G) (S : Finset V) :
    (F.induce (S : Set V)).Copy (G.induce ((S.image f : Finset W) : Set W)) where
  toHom := {
    toFun := fun v => ⟨f v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
    map_rel' := fun h => map_rel f.toHom h
  }
  injective' := fun _ _ h => Subtype.ext (f.injective (congrArg Subtype.val h))

/-- Local induced-density bounds pass to arbitrary copies with the
same order cutoff and coefficient. -/
theorem induced_density_of_copy {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {F : SimpleGraph V} {G : SimpleGraph W} (f : F.Copy G) (K : ℕ) (C : ℝ)
    (hlocal : ∀ S : Finset W, S.card ≤ K →
      ((G.induce (S : Set W)).edgeSet.ncard : ℝ) ≤ C * S.card) :
    ∀ S : Finset V, S.card ≤ K → ((F.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ C * S.card := by
  classical
  intro S hS
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injective S f.injective
  have h := hlocal (S.image f) (by simpa only [hcard] using hS)
  rw [hcard] at h
  apply le_trans _ h
  exact_mod_cast copy_edge_ncard_le (copyInduceImage f S)

theorem sizeRamsey_self_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {F : SimpleGraph V} {G : SimpleGraph W} (e : F ≃g G) :
    SimpleGraph.sizeRamsey F F = SimpleGraph.sizeRamsey G G := by
  apply Nat.le_antisymm
  · exact sizeRamsey_mono ⟨e.toCopy⟩ ⟨e.toCopy⟩
  · exact sizeRamsey_mono ⟨e.symm.toCopy⟩ ⟨e.symm.toCopy⟩

theorem mem_image_equiv_symm {V W : Type*} [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (S : Finset W) (v : V) : v ∈ S.image e.symm ↔ e v ∈ S := by
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
    rw [← hwv, e.apply_symm_apply]
    exact hw
  · intro hv
    exact Finset.mem_image.mpr ⟨e v, hv, e.symm_apply_apply v⟩

end Erdos911
