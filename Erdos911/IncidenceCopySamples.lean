import Erdos911.IncidenceCandidateLists
import Erdos911.CopySeedSamples
import Erdos911.AdaptiveSampling

namespace Erdos911

noncomputable def copyHighNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (v : V) : Finset V := by
  classical
  exact (F.neighborFinset v).filter (fun u => f u ∈ high)

theorem mem_copyHighNeighbors {V W : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (v u : V) :
    u ∈ copyHighNeighbors F f high v ↔ F.Adj v u ∧ f u ∈ high := by
  classical
  simp only [copyHighNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]

theorem copyHighNeighbors_card_le {V W : Type*} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (v : V) :
    (copyHighNeighbors F f high v).card ≤ F.degree v := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem copy_seed_high_flag_image {V W : Type*} [Fintype V] [DecidableEq V]
    {F : SimpleGraph V} [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (S : Finset V) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set V)).Connected) (ω : V → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : V) :
    (seedHighFlagNeighbors F H high s (seedDescriptionOfCopy f S s hS hconn ω) v).image Subtype.val =
      (copyHighNeighbors F f high v).filter (fun u => ω u = true) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hflag, hhigh⟩ := Finset.mem_filter.mp hu
    have h := (seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mp hflag
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨(F.mem_neighborFinset v u.val).mpr h.2, hhigh⟩, h.1⟩
  · intro hx
    obtain ⟨hxU, hxω⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxF, hxHigh⟩ := Finset.mem_filter.mp hxU
    let u : (S : Set V) := ⟨x, hω x hxω⟩
    refine Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨?_, hxHigh⟩, rfl⟩
    exact (seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mpr
      ⟨hxω, (F.mem_neighborFinset v x).mp hxF⟩

theorem copy_seed_high_flag_count {n : ℕ} {W : Type*}
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (f : F.Copy H) (high : Finset W) (S : Finset (Fin n)) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set (Fin n))).Connected) (ω : Fin n → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : Fin n) :
    ((seedHighFlagNeighbors F H high s (seedDescriptionOfCopy f S s hS hconn ω) v).card : ℝ) =
      sampleCount (copyHighNeighbors F f high v) ω := by
  classical
  have h := congrArg Finset.card (copy_seed_high_flag_image f high S s hS hconn ω hω v)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [sampleCount_eq_card]
  exact_mod_cast h

theorem copy_seed_high_hit_image {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) (high : Finset W)
    (S : Finset (Fin n)) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set (Fin n))).Connected) (ω : Fin n → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : Fin n) (w : W) :
    (seedHighHitNeighbors F H J high s (seedDescriptionOfCopy f S s hS hconn ω) v w).image Subtype.val =
      (candidateSlice (copyHighNeighbors F f high v) (fun j => J.neighborFinset (f j)) w).filter
        (fun j => ω j = true) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hhigh, hJ⟩ := (mem_seedHighHitNeighbors F H J high s
      (seedDescriptionOfCopy f S s hS hconn ω) v w u).mp hu
    obtain ⟨hflag, hhigh⟩ := (mem_seedHighFlagNeighbors F H high s
      (seedDescriptionOfCopy f S s hS hconn ω) v u).mp hhigh
    obtain ⟨hωu, hFu⟩ := (seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mp hflag
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(mem_copyHighNeighbors F f high v u.val).mpr
      ⟨hFu, hhigh⟩, ?_⟩, hωu⟩
    exact (J.mem_neighborFinset (f u.val) w).mpr hJ.symm
  · intro hx
    obtain ⟨hxC, hxω⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxU, hxJ⟩ := Finset.mem_filter.mp hxC
    obtain ⟨hxF, hxHigh⟩ := (mem_copyHighNeighbors F f high v x).mp hxU
    let u : (S : Set (Fin n)) := ⟨x, hω x hxω⟩
    refine Finset.mem_image.mpr ⟨u, (mem_seedHighHitNeighbors F H J high s
      (seedDescriptionOfCopy f S s hS hconn ω) v w u).mpr ⟨?_, ?_⟩, rfl⟩
    · exact (mem_seedHighFlagNeighbors F H high s
        (seedDescriptionOfCopy f S s hS hconn ω) v u).mpr ⟨
        (seedDescriptionOfCopy_flag_neighbor f S s hS hconn ω v u).mpr
          ⟨hxω, hxF⟩, hxHigh⟩
    · exact ((J.mem_neighborFinset (f x) w).mp hxJ).symm

theorem copy_seed_high_hit_count {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    {F : SimpleGraph (Fin n)} [DecidableRel F.Adj] {H : SimpleGraph W}
    (J : SimpleGraph W) [DecidableRel J.Adj] (f : F.Copy H) (high : Finset W)
    (S : Finset (Fin n)) (s : ℕ) (hS : S.card ≤ s)
    (hconn : (F.induce (S : Set (Fin n))).Connected) (ω : Fin n → Bool)
    (hω : ∀ v, ω v = true → v ∈ S) (v : Fin n) (w : W) :
    ((seedHighHitNeighbors F H J high s (seedDescriptionOfCopy f S s hS hconn ω) v w).card : ℝ) =
      sampleCount (candidateSlice (copyHighNeighbors F f high v)
        (fun j => J.neighborFinset (f j)) w) ω := by
  classical
  have h := congrArg Finset.card (copy_seed_high_hit_image J f high S s hS hconn ω hω v w)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [sampleCount_eq_card]
  exact_mod_cast h

/-- Adaptive sampling only tests high neighbors at right roles; the left
degrees need not be bounded by the right degree `d`. -/
theorem exists_adaptive_incidence_seed {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (hF : F.Connected) (f : F.Copy H)
    (right : Finset (Fin n)) (high : Finset W) (d D s : ℕ)
    (hd : 0 < d) (hdD : d ≤ D) (hmin : ∀ v, d ≤ F.degree v)
    (hright : ∀ v ∈ right, F.degree v ≤ d) (hhost : ∀ w, J.degree w ≤ D)
    (p ε : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hseed : 3 * n * (p + Real.exp (-(p * d)) + 2 * Real.exp (-(p * d) / 2048) +
      (4 * (D * D : ℕ) + 1 : ℝ) * Real.exp (-(ε ^ 2 * (p * d)) / 512)) ≤ s) :
    ∃ c : SeedDescription F H s,
      seedMapAgrees F H s c f ∧
      ∀ v ∈ right, v ∉ c.1.val →
        |((seedHighFlagNeighbors F H high s c v).card : ℝ) -
          p * (copyHighNeighbors F f high v).card| ≤ p * d / 16 ∧
        (d ≤ 4 * (copyHighNeighbors F f high v).card →
          0 < (seedHighFlagNeighbors F H high s c v).card ∧ ∀ w : W,
            |((seedHighHitNeighbors F H J high s c v w).card : ℝ) /
                (seedHighFlagNeighbors F H high s c v).card -
              ((candidateSlice (copyHighNeighbors F f high v)
                (fun j => J.neighborFinset (f j)) w).card : ℝ) /
                (copyHighNeighbors F f high v).card| ≤ ε) := by
  classical
  let U := fun v => if v ∈ right then copyHighNeighbors F f high v else ∅
  let N := fun j => J.neighborFinset (f j)
  have hU : ∀ v, (U v).card ≤ d := by
    intro v
    by_cases hv : v ∈ right
    · exact (by simpa only [U, ite_eq_left hv] using
        (copyHighNeighbors_card_le F f high v).trans (hright v hv))
    · simp only [U, ite_eq_right hv, Finset.card_empty, Nat.zero_le]
  have hN : ∀ j, (N j).card ≤ D := fun j => hhost (f j)
  obtain ⟨ω, S, hflags, hconn, hacc, hsize⟩ := exists_adaptive_connected_seed F hF U N d D
    hd hdD hmin hU hN p ε hp₀ hp₁ hε₀ hε₁
  have hScard : S.card ≤ s := by exact_mod_cast hsize.trans hseed
  let c := seedDescriptionOfCopy f S s hScard hconn ω
  refine ⟨c, (by intro u; rfl), ?_⟩
  intro v hv hvS
  have haccv := hacc v hvS
  simp only [U, ite_eq_left hv] at haccv
  have hflag := copy_seed_high_flag_count f high S s hScard hconn ω hflags v
  refine ⟨?_, ?_⟩
  · rw [hflag]
    exact haccv.2.1
  · intro hlarge
    obtain ⟨hpos, hfrac⟩ := haccv.2.2 hlarge
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) < (seedHighFlagNeighbors F H high s c v).card := by
        rw [hflag]
        exact hpos
      exact_mod_cast this
    · intro w
      rw [hflag, copy_seed_high_hit_count J f high S s hScard hconn ω hflags v w]
      exact hfrac w

end Erdos911
