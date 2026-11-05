import Erdos911.IncidenceCopySamples

namespace Erdos911

def IncidenceSeedAccurate {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d s : ℕ) (p ε : ℝ) (c : SeedDescription F H s) : Prop :=
  ∀ v ∈ right, v ∉ c.1.val →
    |((seedHighFlagNeighbors F H high s c v).card : ℝ) -
      p * (copyHighNeighbors F f high v).card| ≤ p * d / 16 ∧
    (d ≤ 4 * (copyHighNeighbors F f high v).card →
      0 < (seedHighFlagNeighbors F H high s c v).card ∧ ∀ w : W,
        |((seedHighHitNeighbors F H J high s c v w).card : ℝ) /
            (seedHighFlagNeighbors F H high s c v).card -
          ((candidateSlice (copyHighNeighbors F f high v)
            (fun j => J.neighborFinset (f j)) w).card : ℝ) /
            (copyHighNeighbors F f high v).card| ≤ ε)

theorem copy_high_candidateSlice_card {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (high : Finset W) (v : Fin n) (w : W) :
    (candidateSlice (copyHighNeighbors F f high v) (fun j => J.neighborFinset (f j)) w).card =
      (((copyHighNeighbors F f high v).image f).filter (J.Adj w)).card := by
  have heq : candidateSlice (copyHighNeighbors F f high v) (fun j => J.neighborFinset (f j)) w =
      (copyHighNeighbors F f high v).filter (fun j => J.Adj w (f j)) := by
    ext j
    simp only [candidateSlice, Finset.mem_filter, SimpleGraph.mem_neighborFinset, J.adj_comm]
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (show Function.Injective (f : Fin n → W) from f.injective), heq]

theorem incidence_tested_role_large {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d s : ℕ) (p ε τ : ℝ) (hp : 0 < p) (c : SeedDescription F H s)
    (hacc : IncidenceSeedAccurate F H J f right high d s p ε c)
    (v : Fin n) (w : W) (hw : w ∈ incidenceCandidateList F H J right high d s p τ c v) :
    d ≤ 4 * (copyHighNeighbors F f high v).card := by
  obtain ⟨hv, hvS, _, htest, _, _⟩ :=
    (mem_incidenceCandidateList F H J right high d s p τ c v w).mp hw
  have h := tested_role_is_large _ p (copyHighNeighbors F f high v).card d hp
    (hacc v hv hvS).1 htest
  have hreal : (d : ℝ) ≤ 4 * (copyHighNeighbors F f high v).card := by linarith
  exact_mod_cast hreal

theorem incidence_candidate_fraction_lower {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d s : ℕ) (hd : 0 < d) (p ε : ℝ) (hp : 0 < p) (c : SeedDescription F H s)
    (hacc : IncidenceSeedAccurate F H J f right high d s p ε c)
    (v : Fin n) (w : W)
    (hw : w ∈ incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v) :
    (1 - 5 * ε) * (copyHighNeighbors F f high v).card ≤
      ((candidateSlice (copyHighNeighbors F f high v)
        (fun j => J.neighborFinset (f j)) w).card : ℝ) := by
  have hlarge := incidence_tested_role_large F H J f right high d s p ε (1 - 4 * ε) hp c hacc v w hw
  obtain ⟨hv, hvS, hpos, _, _, hscore⟩ :=
    (mem_incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v w).mp hw
  have hposR : (0 : ℝ) < (seedHighFlagNeighbors F H high s c v).card := by exact_mod_cast hpos
  have hscore' := (le_div_iff₀ hposR).mpr hscore
  have haccuracy := ((hacc v hv hvS).2 hlarge).2 w
  have hU : (0 : ℝ) < (copyHighNeighbors F f high v).card := by
    exact_mod_cast (show 0 < (copyHighNeighbors F f high v).card by omega)
  apply (le_div_iff₀ hU).mp
  linarith [(abs_le.mp haccuracy).2]

/-- The absence of first-scale dense rectangles bounds every tested list.
Only a quarter of the right degree is required in the actual high neighborhood. -/
theorem incidenceCandidateList_card_lt {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d s q : ℕ) (hd : 0 < d) (hq : 0 < q) (hsmall : 8 * q ≤ d)
    (p ε ρ : ℝ) (hp : 0 < p) (hρ : 0 ≤ ρ)
    (hgap : ρ * d + 4 * q < (1 - 5 * ε) * d)
    (hnodense : ∀ A B : Finset W, A.card = q → B.card = q → Disjoint A B →
      (crossEdges J A B : ℝ) ≤ ρ * q * q)
    (c : SeedDescription F H s) (hacc : IncidenceSeedAccurate F H J f right high d s p ε c)
    (v : Fin n) : (incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v).card < q := by
  classical
  by_cases hnonempty : (incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v).Nonempty
  · obtain ⟨w, hw⟩ := hnonempty
    have hlarge := incidence_tested_role_large F H J f right high d s p ε (1 - 4 * ε) hp c hacc v w hw
    let U := (copyHighNeighbors F f high v).image f
    have hUcard : U.card = (copyHighNeighbors F f high v).card :=
      Finset.card_image_of_injective _ (show Function.Injective (f : Fin n → W) from f.injective)
    have hU : 2 * q ≤ U.card := by omega
    have hquarter : (d : ℝ) ≤ 4 * U.card := by exact_mod_cast (hUcard ▸ hlarge)
    have hcoef : 0 ≤ 1 - 5 * ε - ρ := by
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      nlinarith only [hgap, Nat.cast_nonneg (α := ℝ) q, hdR]
    have hUgap : ρ * U.card + q < (1 - 5 * ε) * U.card := by
      have hscale := mul_le_mul_of_nonneg_left hquarter hcoef
      nlinarith only [hscale, hgap]
    apply candidate_list_card_lt J U _ q ρ hq hρ hU hnodense
    intro x hx
    have hdense := incidence_candidate_fraction_lower F H J f right high d s hd p ε hp c hacc v x hx
    rw [copy_high_candidateSlice_card F H J f high v x] at hdense
    rw [← hUcard] at hdense
    exact hUgap.trans_le hdense
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty] using hq

theorem incidence_true_image_mem {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d s : ℕ) (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (c : SeedDescription F H s)
    (hacc : IncidenceSeedAccurate F H J f right high d s p ε c)
    (v : Fin n) (hv : v ∈ right) (hvS : v ∉ c.1.val) (hvLow : f v ∉ high)
    (hlarge : (d : ℝ) / 2 ≤ (copyHighNeighbors F f high v).card)
    (hretained : 1 - 2 * ε ≤
      ((candidateSlice (copyHighNeighbors F f high v)
        (fun j => J.neighborFinset (f j)) (f v)).card : ℝ) /
          (copyHighNeighbors F f high v).card) :
    f v ∈ incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v := by
  have hquarter : d ≤ 4 * (copyHighNeighbors F f high v).card := by
    have hnonneg : (0 : ℝ) ≤ (copyHighNeighbors F f high v).card := Nat.cast_nonneg _
    have hreal : (d : ℝ) ≤ 4 * (copyHighNeighbors F f high v).card := by linarith
    exact_mod_cast hreal
  obtain ⟨hpos, haccuracy⟩ := (hacc v hv hvS).2 hquarter
  have htest := large_role_is_tested _ p (copyHighNeighbors F f high v).card d hp
    (hacc v hv hvS).1 hlarge
  apply (mem_incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v (f v)).mpr
  refine ⟨hv, hvS, hpos, htest, hvLow, ?_⟩
  have hposR : (0 : ℝ) < (seedHighFlagNeighbors F H high s c v).card := by exact_mod_cast hpos
  apply (le_div_iff₀ hposR).mp
  linarith [(abs_le.mp (haccuracy (f v))).1]

theorem incidence_true_image_mem_of_tested {n : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] (H J : SimpleGraph W)
    [DecidableRel J.Adj] (f : F.Copy H) (right : Finset (Fin n)) (high : Finset W)
    (d s : ℕ) (p ε : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (c : SeedDescription F H s)
    (hacc : IncidenceSeedAccurate F H J f right high d s p ε c)
    (v : Fin n) (hne : (incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v).Nonempty)
    (hvLow : f v ∉ high)
    (hretained : 1 - 2 * ε ≤
      ((candidateSlice (copyHighNeighbors F f high v)
        (fun j => J.neighborFinset (f j)) (f v)).card : ℝ) /
          (copyHighNeighbors F f high v).card) :
    f v ∈ incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v := by
  obtain ⟨w, hw⟩ := hne
  have hlarge := incidence_tested_role_large F H J f right high d s p ε (1 - 4 * ε) hp c hacc v w hw
  obtain ⟨hv, hvS, hpos, htest, _, _⟩ :=
    (mem_incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v w).mp hw
  have haccuracy := ((hacc v hv hvS).2 hlarge).2 (f v)
  apply (mem_incidenceCandidateList F H J right high d s p (1 - 4 * ε) c v (f v)).mpr
  refine ⟨hv, hvS, hpos, htest, hvLow, ?_⟩
  have hposR : (0 : ℝ) < (seedHighFlagNeighbors F H high s c v).card := by exact_mod_cast hpos
  apply (le_div_iff₀ hposR).mp
  linarith [(abs_le.mp haccuracy).1]

end Erdos911
