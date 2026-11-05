import Erdos911.CandidateSampling
import Erdos911.OrdinaryRoleEdges

namespace Erdos911

noncomputable def seedDescriptionOfCopy {V W : Type*} [Fintype V]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (S : Finset V)
    (s : ℕ) (hS : S.card ≤ s) (hconn : (F.induce (S : Set V)).Connected)
    (ω : V → Bool) : SeedDescription F H s := by
  classical
  exact ⟨⟨S, hS, hconn⟩, (f.comp (SimpleGraph.Copy.induce F (S : Set V))).toHom,
    Finset.univ.filter (fun v : (S : Set V) => ω v.val = true)⟩

theorem seedDescriptionOfCopy_map {V W : Type*} [Fintype V]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (S : Finset V)
    (s : ℕ) (hS : S.card ≤ s) (hconn : (F.induce (S : Set V)).Connected)
    (ω : V → Bool) (v : (S : Set V)) :
    (seedDescriptionOfCopy f S s hS hconn ω).2.1 v = f v.val := rfl

theorem seedDescriptionOfCopy_flag_neighbor {V W : Type*} [Fintype V]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (S : Finset V)
    (s : ℕ) (hS : S.card ≤ s) (hconn : (F.induce (S : Set V)).Connected)
    (ω : V → Bool) (v : V) (u : (S : Set V)) :
    u ∈ seedFlagNeighbors F H s (seedDescriptionOfCopy f S s hS hconn ω) v ↔
      ω u.val = true ∧ F.Adj v u.val := by
  classical
  change u ∈ ((Finset.univ : Finset (S : Set V)).filter (fun x => ω x.val = true)).filter
    (fun x => F.Adj v x.val) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem copy_seed_flag_image {V W : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (S : Finset V) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set V)).Connected) (ω : V → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : V) :
    (seedFlagNeighbors F H s (seedDescriptionOfCopy f S s hS hconn ω) v).image Subtype.val =
      (F.neighborFinset v).filter (fun u => ω u = true) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have h := (seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mp hu
    exact Finset.mem_filter.mpr ⟨(F.mem_neighborFinset v u.val).mpr h.2, h.1⟩
  · intro hx
    obtain ⟨hFx, hxω⟩ := Finset.mem_filter.mp hx
    let u : (S : Set V) := ⟨x, hω x hxω⟩
    exact Finset.mem_image.mpr ⟨u,
      (seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mpr
        ⟨hxω, (F.mem_neighborFinset v x).mp hFx⟩, rfl⟩

theorem copy_seed_flag_count {n : ℕ} {W : Type*}
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (S : Finset (Fin n)) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set (Fin n))).Connected) (ω : Fin n → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : Fin n) :
    ((seedFlagNeighbors F H s (seedDescriptionOfCopy f S s hS hconn ω) v).card : ℝ) =
      sampleCount (F.neighborFinset v) ω := by
  classical
  have h := congrArg Finset.card (copy_seed_flag_image f S s hS hconn ω hω v)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [sampleCount_eq_card]
  exact_mod_cast h

theorem copy_seed_hit_image {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H)
    (S : Finset (Fin n)) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set (Fin n))).Connected) (ω : Fin n → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : Fin n) (w : W) :
    (seedHitNeighbors F H J s (seedDescriptionOfCopy f S s hS hconn ω) v w).image Subtype.val =
      (candidateSlice (F.neighborFinset v) (fun j => J.neighborFinset (f j)) w).filter
        (fun j => ω j = true) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hflag, hJu⟩ := (mem_seedHitNeighbors F H J s
      (seedDescriptionOfCopy f S s hS hconn ω) v w u).mp hu
    obtain ⟨hωu, hFu⟩ := (seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mp hflag
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(F.mem_neighborFinset v u.val).mpr hFu, ?_⟩, hωu⟩
    exact (J.mem_neighborFinset (f u.val) w).mpr hJu.symm
  · intro hx
    obtain ⟨hxC, hxω⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxF, hxJ⟩ := Finset.mem_filter.mp hxC
    let u : (S : Set (Fin n)) := ⟨x, hω x hxω⟩
    apply Finset.mem_image.mpr
    refine ⟨u, (mem_seedHitNeighbors F H J s (seedDescriptionOfCopy f S s hS hconn ω) v w u).mpr ?_, rfl⟩
    exact ⟨(seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mpr
      ⟨hxω, (F.mem_neighborFinset v x).mp hxF⟩,
      ((J.mem_neighborFinset (f x) w).mp hxJ).symm⟩

theorem copy_seed_hit_count {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H)
    (S : Finset (Fin n)) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set (Fin n))).Connected) (ω : Fin n → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : Fin n) (w : W) :
    ((seedHitNeighbors F H J s (seedDescriptionOfCopy f S s hS hconn ω) v w).card : ℝ) =
      sampleCount (candidateSlice (F.neighborFinset v) (fun j => J.neighborFinset (f j)) w) ω := by
  classical
  have h := congrArg Finset.card (copy_seed_hit_image J f S s hS hconn ω hω v w)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [sampleCount_eq_card]
  exact_mod_cast h

end Erdos911
