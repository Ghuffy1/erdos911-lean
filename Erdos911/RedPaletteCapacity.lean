import Erdos911.PaletteColoring
import Erdos911.VertexDeletion

open MeasureTheory

namespace Erdos911

/-- A fixed connected pattern of sufficiently large average degree has
many distinct label pairs in every host copy, including irregular patterns. -/
theorem red_pattern_distinct_pairs {V W A : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] [DecidableEq A]
    (F : SimpleGraph V) [DecidableRel F.Adj] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hF : F.Connected) (f : F.Copy H) (c : W → A) (d K k : ℕ) (σ : ℝ)
    (hk : 0 < k) (hσ : 0 ≤ σ) (hcard : Fintype.card V ≤ K)
    (hloc : ∀ u v w, H.Adj u v → H.Adj u w → c v = c w → v = w)
    (hrep : ∀ S : Finset W, S.card ≤ K → (H.induce (S : Set W)).Connected →
      k * (repeatedVertices S c).card ≤ 2 * S.card)
    (hlocal : ∀ S : Finset V, S.card ≤ K →
      ((F.induce (S : Set V)).edgeSet.ncard : ℝ) ≤ σ * S.card)
    (hmargin : 256 * σ ≤ (k : ℝ) * d)
    (hdense : (d : ℝ) * Fintype.card V ≤ 16 * F.edgeSet.ncard) :
    (d : ℝ) * Fintype.card V ≤ 32 * ((copyRawEdges f).image (Sym2.map c)).card := by
  classical
  let labels : V → A := c ∘ f
  let S : Finset V := Finset.univ
  have hcopyCard : (S.image f).card = Fintype.card V := by
    have hfi : Function.Injective (f : V → W) := f.injective
    rw [Finset.card_image_of_injective _ hfi, Finset.card_univ]
  have hcopyConn : (H.induce (S.image f : Set W)).Connected := by
    simpa only [S, copyVertices] using copyVertices_connected f hF
  have hsrcrep : k * (repeatedVertices S labels).card ≤ 2 * Fintype.card V := by
    have h := hrep (S.image f) (hcopyCard ▸ hcard) hcopyConn
    rwa [repeatedVertices_image_card S f f.injective c, hcopyCard] at h
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrepsize : ((repeatedVertices S labels).card : ℝ) ≤ 2 * Fintype.card V / k := by
    apply (le_div_iff₀ hkR).mpr
    exact_mod_cast (by simpa only [Nat.mul_comm] using hsrcrep)
  have hcoeff : 2 * σ / k ≤ (d : ℝ) / 128 := by
    apply (div_le_iff₀ hkR).mpr
    nlinarith only [hmargin]
  have hcost : σ * (repeatedVertices S labels).card ≤ (d : ℝ) * Fintype.card V / 128 := by
    calc
      _ ≤ σ * (2 * Fintype.card V / k) := mul_le_mul_of_nonneg_left hrepsize hσ
      _ = (2 * σ / k) * Fintype.card V := by ring
      _ ≤ ((d : ℝ) / 128) * Fintype.card V := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)
      _ = _ := by ring
  have hrsize : (repeatedVertices S labels).card ≤ K :=
    (Finset.card_le_univ _).trans hcard
  have hbound := distinct_label_pairs_density_bound F S labels
    (locally_injective_palette_for_copy f c hloc) σ (hlocal _ hrsize)
  have hcount : (F.induce (S : Set V)).edgeSet.ncard = F.edgeSet.ncard :=
    edge_ncard_induce_of_support_subset F _ (fun _ _ => Finset.mem_univ _)
  rw [hcount] at hbound
  have hsub : (distinctLabelEdges F S labels).image (Sym2.map labels) ⊆
      (copyRawEdges f).image (Sym2.map c) := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have haF : a ∈ F.edgeFinset := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).1
    have hraw : Sym2.map f a ∈ copyRawEdges f :=
      (mem_copyRawEdges_iff_exists f _).mpr ⟨⟨a, F.mem_edgeFinset.mp haF⟩, rfl⟩
    refine Finset.mem_image.mpr ⟨Sym2.map f a, hraw, ?_⟩
    induction a using Sym2.inductionOn with
    | _ u v => rfl
  have hsmall : (((distinctLabelEdges F S labels).image (Sym2.map labels)).card : ℝ) ≤
      ((copyRawEdges f).image (Sym2.map c)).card := by exact_mod_cast Finset.card_le_card hsub
  have hnonneg : (0 : ℝ) ≤ ((copyRawEdges f).image (Sym2.map c)).card := Nat.cast_nonneg _
  nlinarith only [hcost, hbound, hsmall, hdense, hnonneg]

theorem paletteRedEvent_exp_bound {V W A : Type*}
    [Fintype V] [Fintype W] [Fintype A] [DecidableEq A]
    {F : SimpleGraph V} {H : SimpleGraph W} (f : F.Copy H) (c : W → A)
    (p r : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hpair : r ≤ ((copyRawEdges f).image (Sym2.map c)).card) :
    (bitProductMeasure (Sym2 A) p hp0 hp1).real (paletteRedEvent f c) ≤ Real.exp (-p * r) := by
  rw [paletteRedEvent_probability]
  apply (unmarked_probability_exp_bound p hp1 _).trans
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hpair hp0]

theorem anchored_red_palette_decay (D u : ℕ) (d p : ℝ)
    (hD : 2 ≤ D) (hu : 0 < u) (hscale : 256 * Real.log D ≤ p * d) :
    (u * D ^ (2 * (u - 1)) : ℕ) * Real.exp (-p * (d * u / 32)) ≤ 1 / (D : ℝ) ^ 2 := by
  have hDP : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hlog : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have huPow : u ≤ D ^ u := (Nat.le_of_lt u.lt_two_pow_self).trans (Nat.pow_le_pow_left hD u)
  have hcount : u * D ^ (2 * (u - 1)) ≤ D ^ (3 * u) := by
    calc
      _ ≤ D ^ u * D ^ (2 * u) := Nat.mul_le_mul huPow (Nat.pow_le_pow_right (by omega) (by omega))
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hcountExp : ((u * D ^ (2 * (u - 1)) : ℕ) : ℝ) ≤ Real.exp ((3 * u : ℕ) * Real.log D) := by
    have heq : Real.exp (((3 * u : ℕ) : ℝ) * Real.log D) = (D : ℝ) ^ (3 * u) := by
      rw [Real.exp_nat_mul, Real.exp_log hDP]
    rw [heq]
    exact_mod_cast hcount
  have hscaleU := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg (α := ℝ) u)
  calc
    _ ≤ Real.exp (((3 * u : ℕ) : ℝ) * Real.log D) * Real.exp (-8 * (u : ℝ) * Real.log D) := by
      apply mul_le_mul hcountExp (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (Real.exp_pos _).le
      nlinarith only [hscaleU]
    _ = Real.exp (-5 * (u : ℝ) * Real.log D) := by rw [← Real.exp_add]; push_cast; congr 1; ring
    _ ≤ Real.exp (-2 * Real.log D) := by
      apply Real.exp_le_exp.mpr
      have huR : (1 : ℝ) ≤ u := by exact_mod_cast hu
      nlinarith only [mul_le_mul_of_nonneg_right huR hlog, hlog]
    _ = 1 / (D : ℝ) ^ 2 := by
      rw [neg_mul, Real.exp_neg, show (2 : ℝ) * Real.log D = (2 : ℕ) * Real.log D by norm_num,
        Real.exp_nat_mul, Real.exp_log hDP, one_div]

end Erdos911
