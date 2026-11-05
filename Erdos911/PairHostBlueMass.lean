import Erdos911.PairHostColoring
import Erdos911.PairBlueCapacity
import Erdos911.IncidenceRowDeletion

namespace Erdos911

/-- A blue incidence copy can use at most half the full row capacity,
apart from explicitly charged missing roles and bad marked rows. -/
theorem pair_host_blue_mass_bound {L R V : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V]
    (S : R → Finset L) (d : ℕ) (hrow : ∀ y, (S y).card = d)
    (K : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B)
    (ω : Sym2 V → Bool) (l : L → V) (hl : Function.Injective l)
    (r : R → V) (hr : Function.Injective r)
    (hblue : ∀ y x, x ∈ S y → (K \ pairHostRed K A B ω).Adj (l x) (r y)) :
    2 * (∑ y : R, (S y).card) ≤ d * Fintype.card R +
      2 * (∑ x ∈ Finset.univ.filter (fun x => l x ∉ A), (incidenceColumn S x).card) +
      2 * d * (Finset.univ.filter (fun y => r y ∉ B)).card +
      2 * d * (pairBadRows (restrictedHostRows K A B) d ω).card := by
  classical
  let N := restrictedHostRows K A B
  let HB := pairBadRows N d ω
  let badL := (Finset.univ : Finset L).filter (fun x => l x ∉ A)
  let badR := (Finset.univ : Finset R).filter (fun y => r y ∉ B)
  let badV := HB.image Subtype.val
  let badRows := (Finset.univ : Finset R).filter (fun y => r y ∈ badV)
  let T := deletedIncidenceRows S badL badR badRows
  have hmem (y : R) (x : L) (hx : x ∈ T y) :
      r y ∈ B ∧ r y ∉ badV ∧ x ∈ S y ∧ l x ∈ A := by
    have hh : ¬(y ∈ badR ∨ y ∈ badRows) := by
      intro h
      simp only [T, deletedIncidenceRows, h, ite_true, Finset.notMem_empty] at hx
    have hx' : x ∈ S y \ badL := by
      simpa only [T, deletedIncidenceRows, hh, ite_false] using hx
    obtain ⟨hxS, hxL⟩ := Finset.mem_sdiff.mp hx'
    have hrB : r y ∈ B := by
      by_contra h
      exact hh (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hrV : r y ∉ badV := by
      intro h
      exact hh (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hlA : l x ∈ A := by
      by_contra h
      exact hxL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact ⟨hrB, hrV, hxS, hlA⟩
  let N' : Option ↥B → Finset V := fun z => z.elim ∅ N
  let r' : R → Option ↥B := fun y => if h : r y ∈ B then some ⟨r y, h⟩ else none
  have hmap (y : R) (hy : r y ∈ B) : r' y = some ⟨r y, hy⟩ := by
    simp only [r', hy, dite_true]
  have hretblue (y : R) (x : L) (hx : x ∈ T y) : l x ∈ pairBlueRow (N' (r' y)) ω := by
    obtain ⟨hy, _, hxS, hxA⟩ := hmem y x hx
    rw [hmap y hy]
    exact pairHostBlue_between K A B ω hAB _ _ hxA hy (hblue y x hxS)
  have hgood (y : R) (hy : (T y).Nonempty) : r' y ∉ pairBadRows N' d ω := by
    obtain ⟨x, hx⟩ := hy
    obtain ⟨hyB, hyV, _, _⟩ := hmem y x hx
    rw [hmap y hyB]
    intro hbad
    have hbad' : (⟨r y, hyB⟩ : ↥B) ∈ HB := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hbad).2⟩
    exact hyV (Finset.mem_image.mpr ⟨⟨r y, hyB⟩, hbad', rfl⟩)
  have hcap := pair_blue_incidence_capacity T N' l hl r' d ω hretblue hgood
  have hrows : badRows.card ≤ HB.card := by
    calc
      badRows.card = (badRows.image r).card := (Finset.card_image_of_injective _ hr).symm
      _ ≤ badV.card := Finset.card_le_card (by
        intro v hv
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hy).2)
      _ = HB.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hdel := incidence_row_deletion_bound S badL badR badRows d hrow
  change (∑ y : R, (S y).card) ≤ (∑ y : R, (T y).card) +
    (∑ x ∈ badL, (incidenceColumn S x).card) + d * badR.card + d * badRows.card at hdel
  have hcharge := Nat.mul_le_mul_left d hrows
  change 2 * (∑ y : R, (S y).card) ≤ d * Fintype.card R +
    2 * (∑ x ∈ badL, (incidenceColumn S x).card) + 2 * d * badR.card + 2 * d * HB.card
  nlinarith only [hcap, hdel, hcharge]

end Erdos911
