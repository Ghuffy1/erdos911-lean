import Erdos911.EntropyTypeRatios

namespace Erdos911

theorem entropy_repeated_support_log_gap (d a : ℕ) (M X : ℝ)
    (hd : 1 ≤ d) (hlog : 32768 ≤ Real.log d) (hM : 1 ≤ M) (hMd : M ≤ d)
    (ha : 131072 ≤ a) (hX : X ≤ (1 - 1 / 16384 : ℝ) * a * Real.log d) :
    X ≤ ((1 - 1 / 32768 : ℝ) * Real.log d) * a +
      Real.log (1 / (16 * M * d * Real.log d)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hMpos : 0 < M := by linarith
  have hLpos : 0 < Real.log d := by linarith
  have hlogM : Real.log M ≤ Real.log d := Real.log_le_log hMpos hMd
  have hlogL := Real.log_le_sub_one_of_pos hLpos
  have hlog16 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)
  norm_num at hlog16
  have hdenlog : Real.log (16 * M * d * Real.log d) =
      Real.log 16 + Real.log M + Real.log d + Real.log (Real.log d) := by
    rw [Real.log_mul (by positivity) hLpos.ne', Real.log_mul (by positivity) hdpos.ne',
      Real.log_mul (by norm_num) hMpos.ne']
  have hdenbound : Real.log (16 * M * d * Real.log d) ≤ 4 * Real.log d := by
    rw [hdenlog]
    linarith
  have haR : (131072 : ℝ) ≤ a := by exact_mod_cast ha
  have hmargin := mul_le_mul_of_nonneg_right haR hLpos.le
  rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub]
  nlinarith only [hdenbound, hmargin, hX]

theorem entropy_repeated_type_pruning (B : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ (W : Type*) [Fintype W] [DecidableEq W],
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      0 < n → (∀ v, d ≤ G.degree v) → (∀ v, G.degree v ≤ d ^ B) →
      (SimpleGraph.sizeRamsey G G : ℝ) ≤ (M * d) * G.edgeSet.ncard →
      ∀ (J : SimpleGraph W) [DecidableRel J.Adj],
      (∀ w, J.degree w ≤ d ^ (B + 3)) →
      (∀ S : Finset W, (J.induce (S : Set W)).edgeSet.ncard ≤ entropyHostDensityCutoff d * S.card) →
      ∀ P : Finset (RectangleBlock W), BoundedEdgeBlocks P (baselineBlockSize d * baselineBlockSize d) →
      ∃ t : ComponentType G,
        ((repeatedBadSupport G J P (componentSize G t / 1024) t).card : ℝ) ≤
          J.edgeFinset.card / (16 * M * d * Real.log d) ∧
        ∀ f : (componentModel G t).Copy
            (J.deleteEdges (repeatedBadSupport G J P (componentSize G t / 1024) t : Set (Sym2 W))),
          repeatedEdgeVolume P (copyRawEdges
            ((SimpleGraph.Copy.ofLE _ J (J.deleteEdges_le _)).comp f)) < 3 * (componentSize G t / 1024) := by
  obtain ⟨d₁, hd₁⟩ := polynomial_counterexample_class_lower 2 B
  obtain ⟨d₂, hd₂⟩ := eventually_entropy_host_parameters B M
  obtain ⟨d₃, hd₃⟩ := eventually_entropy_type_log_bounds B M hM
  let d₀ := max 262144 (max d₁ (max d₂ (max d₃ (32768 * (B + 3)))))
  refine ⟨d₀, ?_⟩
  intro d hd W _ _ n G _ hn hmin hmax hcheap J _ hJdegree hJdensity P hP
  classical
  have hdlarge : 262144 ≤ d := (le_max_left _ _).trans hd
  have hdrest : max d₁ (max d₂ (max d₃ (32768 * (B + 3)))) ≤ d := (le_max_right _ _).trans hd
  have hd₁' : d₁ ≤ d := (le_max_left _ _).trans hdrest
  have hrest : max d₂ (max d₃ (32768 * (B + 3))) ≤ d := (le_max_right _ _).trans hdrest
  have hd₂' : d₂ ≤ d := (le_max_left _ _).trans hrest
  have hrest' : max d₃ (32768 * (B + 3)) ≤ d := (le_max_right _ _).trans hrest
  have hd₃' : d₃ ≤ d := (le_max_left _ _).trans hrest'
  have hscale : 32768 * (B + 3) ≤ d := (le_max_right _ _).trans hrest'
  obtain ⟨_, hlog, hloglog, hMd, _, _⟩ := hd₂ d hd₂'
  have hMscale : M * (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hMd (Nat.cast_nonneg (α := ℝ) d)
    nlinarith only [h]
  have hcheap' : (SimpleGraph.sizeRamsey G G : ℝ) ≤ (d : ℝ) ^ 2 * G.edgeSet.ncard :=
    hcheap.trans (mul_le_mul_of_nonneg_right hMscale (Nat.cast_nonneg _))
  obtain ⟨t₀, hclass⟩ := hd₁ d hd₁' n G hn
    (by simpa only [G.ncard_neighborSet] using hmin)
    (by simpa only [G.ncard_neighborSet] using hmax) hcheap'
  let k := componentOrder G t₀
  let a := componentSize G t₀
  have hk : 0 < k := componentOrder_pos G t₀
  have haverage : d * k ≤ 2 * a := component_degree_sum_bound G d hmin t₀
  have hdk : d ≤ d * k := by
    calc
      d = d * 1 := by omega
      _ ≤ d * k := Nat.mul_le_mul_left d (by omega)
  have ha : 131072 ≤ a := by omega
  have hFG : (componentModel G t₀).IsContained G :=
    ⟨SimpleGraph.Copy.induce G (componentRepresentative G t₀).supp⟩
  have hdensity : (a : ℝ) ≤ entropyTargetDensity B M d * k := by
    have h := entropy_target_density_bound (componentModel G t₀) G hFG B d M
      (by omega) hM (by linarith) hmax hcheap
    simpa only [a, k, componentSize, componentOrder, Nat.card_eq_fintype_card] using h
  have hratios := hd₃ d hd₃' k a (by omega) haverage hdensity
  have hthreshold := repeated_threshold_bounds a (by omega)
  have hroot := polynomial_repeated_root_bound (B + 3) d k a (d ^ (B + 3)) hscale
    (by linarith) haverage (Nat.one_le_pow _ _ (by omega)) le_rfl
  have hX := repeated_type_exponent_deficit k a (a / 1024) (d ^ (B + 3))
    (entropyHostDensityCutoff d * k) (baselineBlockSize d * baselineBlockSize d) d hlog
    hroot hratios.1 hratios.2 hthreshold.2
  have hgap := entropy_repeated_support_log_gap d a M
    (repeatedTypeExponent k a (a / 1024) (d ^ (B + 3))
      (entropyHostDensityCutoff d * k) (baselineBlockSize d * baselineBlockSize d))
    (by omega) hlog hM hMd ha hX
  have hMbound : ∀ S : Finset W, S.card = k →
      (J.induce (S : Set W)).edgeSet.ncard ≤ entropyHostDensityCutoff d * k := by
    intro S hS
    simpa only [hS] using hJdensity S
  have hTpos : 0 < entropyHostDensityCutoff d := by
    have h := Nat.le_ceil ((d : ℝ) ^ 2 * (Real.log d) ^ 3)
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hreal : (0 : ℝ) < entropyHostDensityCutoff d :=
      (show 0 < (d : ℝ) ^ 2 * (Real.log d) ^ 3 by positivity).trans_le h
    exact_mod_cast hreal
  have hqpos : 0 < baselineBlockSize d := by
    have h := Nat.le_ceil ((Real.log d) ^ 4)
    have hreal : (0 : ℝ) < baselineBlockSize d := (pow_pos (by linarith : 0 < Real.log d) 4).trans_le h
    exact_mod_cast hreal
  let L := (1 - 1 / 32768 : ℝ) * Real.log d
  have hclass' : Real.exp (L * a) ≤ ((componentClass G k a).card : ℝ) := by
    simpa only [L, a, k, mul_assoc, mul_comm, mul_left_comm] using hclass.le
  have hdenpos : 0 < 16 * M * d * Real.log d := by positivity
  obtain ⟨t, ht, hsupport⟩ := exists_repeated_type_support_of_gap G J P
    (baselineBlockSize d * baselineBlockSize d) hP k a (a / 1024) (d ^ (B + 3))
    (entropyHostDensityCutoff d * k) hJdegree hMbound (by positivity) (Nat.mul_pos hTpos hk)
    (Nat.mul_pos hqpos hqpos) hthreshold.1 L (1 / (16 * M * d * Real.log d))
    (by positivity) hclass' hgap
  have hsize : componentSize G t = a := (mem_componentClass G k a t).mp ht |>.2
  refine ⟨t, ?_, ?_⟩
  · rw [hsize]
    calc
      ((repeatedBadSupport G J P (a / 1024) t).card : ℝ) ≤
          (1 / (16 * M * d * Real.log d)) * J.edgeFinset.card := hsupport
      _ = _ := by ring
  · rw [hsize]
    intro f
    exact Nat.lt_of_not_ge (repeatedBadSupport_eliminates_bad_copies G J P (a / 1024) t (by omega) f)

end Erdos911
