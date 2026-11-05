import Erdos911.ConnectedSetCounts
import Erdos911.BluePaletteExponents

open MeasureTheory

namespace Erdos911

noncomputable def paletteComponentBad {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d : ℕ) : Set (Sym2 A → Bool) :=
  ⋃ S : ↥(paletteBadSets F d), ⋃ f : ↥S.val → A, bluePaletteMapEvent F S.val f

theorem mem_paletteComponentBad {V A : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d : ℕ) (ω : Sym2 A → Bool) :
    ω ∈ paletteComponentBad F d ↔ ∃ (S : Finset V), S ∈ paletteBadSets F d ∧
      ∃ f : ↥S → A, ω ∈ bluePaletteMapEvent F S f := by
  simp only [paletteComponentBad, Set.mem_iUnion]
  constructor
  · rintro ⟨S, f, hf⟩
    exact ⟨S.val, S.property, f, hf⟩
  · rintro ⟨S, hS, f, hf⟩
    exact ⟨⟨S, hS⟩, f, hf⟩

/-- The blue obstruction probability for a bounded component. The
geometric sum is over set orders; no factor exponential in component order
is introduced by summing the connected-set witnesses. -/
theorem paletteComponentBad_probability {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d D : ℕ) (p ℓ : ℝ)
    (hd : 0 < d) (hD : 1 ≤ D) (hmin : ∀ v, d ≤ F.degree v)
    (hmax : ∀ v, F.degree v ≤ D) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hℓ : 0 ≤ ℓ)
    (hbase : 16 * Real.exp 1 * p ≤ Real.exp (-ℓ))
    (hentropy : Real.log (Fintype.card A) + 2 * Real.log D ≤ (d : ℝ) * ℓ / 64)
    (hlog : 128 * Real.log 2 ≤ (d : ℝ) * ℓ) :
    (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteComponentBad F d) ≤
      Fintype.card V * Real.exp (-(d : ℝ) ^ 2 * ℓ / 512) := by
  classical
  let B := paletteBadSets F d
  let orders := B.image Finset.card
  let w (u : ℕ) : ℝ := (Fintype.card A : ℝ) ^ u * Real.exp (-(d : ℝ) * ℓ * u / 32)
  have hinfo (S : ↥B) := (mem_paletteBadSets F d S.val).mp S.property
  have hvolume (S : ↥B) : 0 < degreeVolume F S.val :=
    (Nat.mul_pos hd (hinfo S).1).trans_le (degreeVolume_minimum F d hmin S.val)
  have hprob (S : ↥B) : (bitProductMeasure (Sym2 A) p hp0 hp1).real
      (⋃ f : ↥S.val → A, bluePaletteMapEvent F S.val f) ≤ w S.val.card := by
    apply (exists_bluePaletteMap_probability F S.val (hvolume S) p hp0 hp1).trans
    exact mul_le_mul_of_nonneg_left (palette_blue_tail_exp F d hmin S.val p ℓ hp0 hℓ hbase)
      (by positivity)
  have hunion : (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteComponentBad F d) ≤
      ∑ S ∈ B, w S.card := by
    apply (measureReal_iUnion_fintype_le (fun S : ↥B =>
      ⋃ f : ↥S.val → A, bluePaletteMapEvent F S.val f)).trans
    have h := Finset.sum_le_sum (fun S (_ : S ∈ (Finset.univ : Finset ↥B)) => hprob S)
    rw [Finset.sum_coe_sort B (fun S => w S.card)] at h
    exact h
  have hsum : (∑ S ∈ B, w S.card) =
      ∑ u ∈ orders, ((B.filter (fun S => S.card = u)).card : ℝ) * w u := by
    symm
    calc
      _ = ∑ u ∈ orders, ∑ _S ∈ B.filter (fun S => S.card = u), w u := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ = _ := Finset.sum_fiberwise_of_maps_to'
        (fun S hS => Finset.mem_image.mpr ⟨S, hS, rfl⟩) w
  have horder (u : ℕ) (hu : u ∈ orders) : 0 < u ∧ d ≤ 4 * u := by
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hu
    have hi := (mem_paletteBadSets F d S).mp hS
    exact ⟨hi.1, hi.2.2⟩
  have hpoint (u : ℕ) (hu : u ∈ orders) :
      ((B.filter (fun S => S.card = u)).card : ℝ) * w u ≤
      (Fintype.card V : ℝ) * Real.exp (-(d : ℝ) ^ 2 * ℓ / 512) * (1 / 2 : ℝ) ^ u := by
    have hcount : ((B.filter (fun S => S.card = u)).card : ℝ) ≤
        Fintype.card V * (D : ℝ) ^ (2 * (u - 1)) := by
      exact_mod_cast paletteBadSets_order_card_le F d D u hmax
    have he := palette_order_entropy_bound D (Fintype.card A) d u ℓ hD Fintype.card_pos hℓ hentropy
    have hs := palette_order_decay_split d u ℓ hℓ (horder u hu).2 hlog
    calc
      _ ≤ (Fintype.card V : ℝ) * (D : ℝ) ^ (2 * (u - 1)) * w u :=
        mul_le_mul_of_nonneg_right hcount (by dsimp [w]; positivity)
      _ = (Fintype.card V : ℝ) * ((D : ℝ) ^ (2 * (u - 1)) *
          (Fintype.card A : ℝ) ^ u * Real.exp (-(d : ℝ) * ℓ * u / 32)) := by dsimp [w]; ring
      _ ≤ (Fintype.card V : ℝ) * Real.exp (-(d : ℝ) * ℓ * u / 64) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Fintype.card V : ℝ) * (Real.exp (-(d : ℝ) ^ 2 * ℓ / 512) * (1 / 2 : ℝ) ^ u) :=
        mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
      _ = _ := by ring
  apply hunion.trans
  rw [hsum]
  calc
    _ ≤ ∑ u ∈ orders, (Fintype.card V : ℝ) * Real.exp (-(d : ℝ) ^ 2 * ℓ / 512) * (1 / 2 : ℝ) ^ u :=
      Finset.sum_le_sum hpoint
    _ = ((Fintype.card V : ℝ) * Real.exp (-(d : ℝ) ^ 2 * ℓ / 512)) *
        ∑ u ∈ orders, (1 / 2 : ℝ) ^ u := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (positive_geometric_sum_le_one orders (fun u hu => (horder u hu).1))

theorem paletteComponentBad_probability_small {V A : Type*}
    [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (d D K : ℕ) (p ℓ : ℝ)
    (hd : 0 < d) (hD : 1 ≤ D) (hK : 0 < K) (hcard : Fintype.card V ≤ K)
    (hmin : ∀ v, d ≤ F.degree v) (hmax : ∀ v, F.degree v ≤ D)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hℓ : 0 ≤ ℓ)
    (hbase : 16 * Real.exp 1 * p ≤ Real.exp (-ℓ))
    (hentropy : Real.log (Fintype.card A) + 2 * Real.log D ≤ (d : ℝ) * ℓ / 64)
    (hlog : 128 * Real.log 2 ≤ (d : ℝ) * ℓ)
    (hbudget : Real.log K + Real.log 1000 ≤ (d : ℝ) ^ 2 * ℓ / 512) :
    (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteComponentBad F d) ≤ 1 / 1000 := by
  have hKP : (0 : ℝ) < K := by exact_mod_cast hK
  calc
    _ ≤ (Fintype.card V : ℝ) * Real.exp (-(d : ℝ) ^ 2 * ℓ / 512) :=
      paletteComponentBad_probability F d D p ℓ hd hD hmin hmax hp0 hp1 hℓ hbase hentropy hlog
    _ ≤ (K : ℝ) * Real.exp (-(d : ℝ) ^ 2 * ℓ / 512) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le
    _ = Real.exp (Real.log K - (d : ℝ) ^ 2 * ℓ / 512) := by
      conv_lhs => rw [← Real.exp_log hKP]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log 1000) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / 1000 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

end Erdos911
