import Erdos911.GraphCounting

namespace Erdos911

/-- The degree-and-cover coloring used in the maximum-degree reduction. -/
theorem degree_cover_avoiding {V U W : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (J₀ : SimpleGraph U) [DecidableRel J₀.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hJ₀ : J₀.IsContained J)
    (hbudget : 2 * H.edgeFinset.card * J₀.maxDegree < J.maxDegree * J₀.edgeFinset.card) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬J.IsContained R ∧ ¬J.IsContained (H \ R) := by
  classical
  let d := J.maxDegree
  let S := Finset.univ.filter (fun v => d ≤ H.degree v)
  let R : SimpleGraph W := {
    Adj := fun u v => H.Adj u v ∧ u ∉ S ∧ v ∉ S
    symm := ⟨fun u v h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
    loopless := ⟨fun u h => H.irrefl h.1⟩ }
  have hR : R ≤ H := fun _ _ h => h.1
  have hd : 0 < d := by
    have hp : 0 < d * J₀.edgeFinset.card := (Nat.zero_le _).trans_lt hbudget
    by_contra hzero
    have hz : d = 0 := Nat.eq_zero_of_not_pos hzero
    simp only [hz, zero_mul, lt_self_iff_false] at hp
  have hred : ¬J.IsContained R := by
    rintro ⟨f⟩
    obtain ⟨v, hv⟩ := J.exists_maximal_degree_vertex
    have hdeg : d ≤ R.degree (f v) := by
      change J.maxDegree ≤ R.degree (f v)
      rw [hv]
      exact f.degree_le v
    obtain ⟨w, hw⟩ := (R.degree_pos_iff_exists_adj (f v)).mp (hd.trans_le hdeg)
    have hlow : f v ∉ S := hw.2.1
    have hupper : R.degree (f v) ≤ H.degree (f v) :=
      (SimpleGraph.Copy.ofLE R H hR).degree_le (f v)
    exact hlow (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg.trans hupper⟩)
  have hcover : (H \ R).IsVertexCover (S : Set W) := by
    intro u v h
    rw [SimpleGraph.sdiff_adj] at h
    by_contra hneither
    have hu : u ∉ S := fun hu => hneither (Or.inl hu)
    have hv : v ∉ S := fun hv => hneither (Or.inr hv)
    exact h.2 ⟨h.1, hu, hv⟩
  have hblue₀ : ¬J₀.IsContained (H \ R) := by
    rintro ⟨f⟩
    let T := Finset.univ.filter (fun v : U => f v ∈ S)
    have hTcover : J₀.IsVertexCover (T : Set U) := by
      intro u v huv
      have h := hcover (map_rel f.toHom huv)
      simpa only [T, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.Copy.toHom_apply] using h
    have hTcard : T.card ≤ S.card := by
      calc
        T.card = (T.image f).card := (Finset.card_image_of_injective T f.injective').symm
        _ ≤ S.card := Finset.card_le_card (by
          intro w hw
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
          exact (Finset.mem_filter.mp hv).2)
    have hcapacity : J₀.edgeFinset.card ≤ S.card * J₀.maxDegree := by
      exact (edges_le_cover_card_mul_degree J₀ T J₀.maxDegree hTcover J₀.degree_le_maxDegree).trans
        (Nat.mul_le_mul_right _ hTcard)
    have hhigh : d * S.card ≤ 2 * H.edgeFinset.card := high_degree_card_bound H d
    have hleft := Nat.mul_le_mul_left d hcapacity
    have hright := Nat.mul_le_mul_right J₀.maxDegree hhigh
    have hcontra : d * J₀.edgeFinset.card ≤ 2 * H.edgeFinset.card * J₀.maxDegree := by
      nlinarith only [hleft, hright]
    exact (not_lt_of_ge hcontra) hbudget
  exact ⟨R, hR, hred, fun h => hblue₀ (hJ₀.trans h)⟩

/-- Integer form of the degree-and-cover lower bound for the exact size-Ramsey
definition used in problem 911. -/
theorem degree_cover_size_bound {V U : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (J₀ : SimpleGraph U) [DecidableRel J₀.Adj] (hJ₀ : J₀.IsContained J) :
    J.maxDegree * J₀.edgeFinset.card ≤ 2 * SimpleGraph.sizeRamsey J J * J₀.maxDegree := by
  classical
  by_contra h
  have hstrict := Nat.lt_of_not_ge h
  obtain ⟨n, H, hsize, hH⟩ := sizeRamsey_attained J J
  have hcard : H.edgeFinset.card = SimpleGraph.sizeRamsey J J := by
    rw [H.edgeFinset_card, Set.fintypeCard_eq_ncard]
    exact hsize
  obtain ⟨R, hR, hred, hblue⟩ := degree_cover_avoiding J J₀ H hJ₀
    (by simpa only [hcard] using hstrict)
  exact (hH R hR).elim hred hblue

theorem degree_cover_size_bound_real {V U : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (J₀ : SimpleGraph U) [DecidableRel J₀.Adj] (hJ₀ : J₀.IsContained J)
    (hΔ : 0 < J₀.maxDegree) :
    (J.maxDegree : ℝ) * J₀.edgeSet.ncard / (2 * J₀.maxDegree) ≤
      (SimpleGraph.sizeRamsey J J : ℝ) := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * J₀.maxDegree)).mpr
  have hedge : J₀.edgeSet.ncard = J₀.edgeFinset.card := by
    rw [J₀.edgeFinset_card, Set.fintypeCard_eq_ncard]
  rw [hedge]
  have hbound : (J.maxDegree : ℝ) * J₀.edgeFinset.card ≤
      2 * (SimpleGraph.sizeRamsey J J : ℝ) * J₀.maxDegree := by
    exact_mod_cast degree_cover_size_bound J J₀ hJ₀
  nlinarith only [hbound]

end Erdos911
