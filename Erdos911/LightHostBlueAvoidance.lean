import Erdos911.LightHostRoles
import Erdos911.PairHostBlueMass

namespace Erdos911

/-- The pair marking excludes a blue copy after charging the two
high-degree image sets and the small family of bad host rows. -/
theorem light_host_blue_excludes_target {L R V : Type*}
    [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V]
    (S : R → Finset L) (d : ℕ) (P Δ Λ : ℝ) (DL DR : ℕ)
    (hd : 0 < d) (hDL : 0 < DL) (hDR : 0 < DR) (hΔ : 0 ≤ Δ)
    (hDRP : (DR : ℝ) < P) (hrow : ∀ y, (S y).card = d)
    (hleft : ∀ x, P ≤ (incidenceGraph S).degree (Sum.inl x))
    (hmax : ∀ x, ((incidenceGraph S).degree (Sum.inl x) : ℝ) ≤ Δ)
    (he : 0 < (incidenceGraph S).edgeSet.ncard)
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hbudget : (K.edgeSet.ncard : ℝ) ≤ Λ * (incidenceGraph S).edgeSet.ncard)
    (hcutL : 16 * Λ * Δ ≤ (DL : ℝ)) (hcutR : 16 * Λ * d ≤ (DR : ℝ))
    (ω : Sym2 V → Bool)
    (hbad : ((pairBadRows (restrictedHostRows K (lightHostLeftRole K P DL)
      (lightHostRightRole K DR)) d ω).card : ℝ) ≤
        (incidenceGraph S).edgeSet.ncard / (8 * d)) :
    ¬(incidenceGraph S).IsContained
      (K \ pairHostRed K (lightHostLeftRole K P DL) (lightHostRightRole K DR) ω) := by
  classical
  rintro ⟨g⟩
  let A := lightHostLeftRole K P DL
  let B := lightHostRightRole K DR
  let f : (incidenceGraph S).Copy K := (SimpleGraph.Copy.ofLE _ K sdiff_le).comp g
  let l : L → V := fun x => f (Sum.inl x)
  let r : R → V := fun y => f (Sum.inr y)
  let badL := (Finset.univ : Finset L).filter (fun x => l x ∉ A)
  let badR := (Finset.univ : Finset R).filter (fun y => r y ∉ B)
  have hl : Function.Injective l := fun _ _ h => Sum.inl_injective (f.injective h)
  have hr : Function.Injective r := fun _ _ h => Sum.inr_injective (f.injective h)
  have he0 : (0 : ℝ) ≤ (incidenceGraph S).edgeSet.ncard := by positivity
  have hLimages (x : L) (hx : x ∈ badL) : DL ≤ K.degree (l x) := by
    have hmin : P ≤ (K.degree (l x) : ℝ) :=
      (hleft x).trans (by exact_mod_cast f.degree_le (Sum.inl x))
    have hn := (Finset.mem_filter.mp hx).2
    have hnot : ¬K.degree (l x) ≤ DL := by
      intro hh
      exact hn ((mem_lightHostLeftRole K P DL (l x)).mpr ⟨hmin, hh⟩)
    omega
  have hRimages (y : R) (hy : y ∈ badR) : DR ≤ K.degree (r y) := by
    have hmin : d ≤ K.degree (r y) := by
      have hh := f.degree_le (Sum.inr y)
      rw [incidenceGraph_degree_right, hrow] at hh
      exact hh
    have hn := (Finset.mem_filter.mp hy).2
    have hnot : ¬K.degree (r y) ≤ DR := by
      intro hh
      exact hn ((mem_lightHostRightRole K DR (r y)).mpr ⟨lt_of_lt_of_le hd hmin, hh⟩)
    omega
  have hLmass : (∑ x ∈ badL, ((incidenceColumn S x).card : ℝ)) ≤
      (incidenceGraph S).edgeSet.ncard / 8 := by
    apply high_image_weight_sum_le K l hl badL (fun x => (incidenceColumn S x).card)
      DL Δ Λ ((incidenceGraph S).edgeSet.ncard) hDL hΔ he0
    · intro x _
      simpa only [incidenceGraph_degree_left, incidenceColumn] using hmax x
    · exact hLimages
    · exact hbudget
    · exact hcutL
  have hRmass : (d : ℝ) * badR.card ≤ (incidenceGraph S).edgeSet.ncard / 8 := by
    have hh := high_image_weight_sum_le K r hr badR (fun _ => (d : ℝ))
      DR d Λ ((incidenceGraph S).edgeSet.ncard) hDR (Nat.cast_nonneg _) he0
      (fun _ _ => le_rfl) hRimages hbudget hcutR
    simpa [mul_comm] using hh
  have hbadmass : (d : ℝ) * (pairBadRows (restrictedHostRows K A B) d ω).card ≤
      (incidenceGraph S).edgeSet.ncard / 8 := by
    have hh := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg (α := ℝ) d)
    have hdp : (0 : ℝ) < d := by exact_mod_cast hd
    convert hh using 1
    field_simp
  have hblue (y : R) (x : L) (hx : x ∈ S y) :
      (K \ pairHostRed K A B ω).Adj (l x) (r y) :=
    map_rel g.toHom (show (incidenceGraph S).Adj (Sum.inl x) (Sum.inr y) from hx)
  have hmass := pair_host_blue_mass_bound S d hrow K A B
    (lightHostRoles_disjoint K P DL DR hDRP) ω l hl r hr hblue
  have hedge : (incidenceGraph S).edgeSet.ncard = ∑ y : R, (S y).card := by
    rw [← Set.fintypeCard_eq_ncard, ← (incidenceGraph S).edgeFinset_card, incidenceGraph_edge_count]
  have hcount : (∑ y : R, (S y).card) = d * Fintype.card R := by simp [hrow, mul_comm]
  have hmassR : 2 * ((incidenceGraph S).edgeSet.ncard : ℝ) ≤
      (incidenceGraph S).edgeSet.ncard +
      2 * (∑ x ∈ badL, ((incidenceColumn S x).card : ℝ)) +
      2 * d * badR.card + 2 * d * (pairBadRows (restrictedHostRows K A B) d ω).card := by
    rw [← hcount] at hmass
    rw [← hedge] at hmass
    exact_mod_cast hmass
  have hepos : (0 : ℝ) < (incidenceGraph S).edgeSet.ncard := by exact_mod_cast he
  nlinarith only [hmassR, hLmass, hRmass, hbadmass, hepos]

end Erdos911
