import Erdos911.BiasedBits
import Erdos911.ExponentialCoordinateLLL

open MeasureTheory

namespace Erdos911

/-- Finite conditional first moment for the total cost of marked events. -/
theorem exists_conditional_cost_le {Ω I : Type*} [Fintype Ω] [Fintype I]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Good : Set Ω)
    (hGood : 0 < μ.real Good) (A : I → Set Ω) (c b : I → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hprob : ∀ i, μ.real (A i ∩ Good) / μ.real Good ≤ b i) :
    ∃ ω ∈ Good, (∑ i, (A i).indicator (fun _ => c i) ω) ≤ ∑ i, b i * c i := by
  classical
  let S := Finset.univ.filter (fun ω => ω ∈ Good)
  have hSset : (S : Set Ω) = Good := by ext ω; simp [S]
  have hS : S.Nonempty := by
    by_contra h
    have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hGoodEmpty : Good = ∅ := by rw [← hSset, hEmpty, Finset.coe_empty]
    rw [hGoodEmpty, measureReal_empty] at hGood
    exact lt_irrefl 0 hGood
  let cost (ω : Ω) := ∑ i, (A i).indicator (fun _ => c i) ω
  have hmass : ∑ ω ∈ S, μ.real {ω} = μ.real Good := by
    rw [sum_measureReal_singleton, hSset]
  have hsingle (i : I) :
      (∑ ω ∈ S, μ.real {ω} * (if ω ∈ A i then c i else 0)) =
        μ.real (A i ∩ Good) * c i := by
    have hset : ((S.filter (fun ω => ω ∈ A i) : Finset Ω) : Set Ω) = A i ∩ Good := by
      ext ω
      simp only [Finset.mem_coe, Finset.mem_filter, S, Finset.mem_univ, true_and,
        Set.mem_inter_iff]
      exact and_comm
    calc
      _ = (∑ ω ∈ S.filter (fun ω => ω ∈ A i), μ.real {ω}) * c i := by
        conv_rhs => rw [Finset.sum_mul, Finset.sum_filter]
        exact Finset.sum_congr rfl (fun ω _ => by split_ifs <;> simp_all)
      _ = μ.real (A i ∩ Good) * c i := by rw [sum_measureReal_singleton, hset]
  have hsum : ∑ ω ∈ S, μ.real {ω} * cost ω ≤
      (∑ i, b i * c i) * μ.real Good := by
    calc
      _ = ∑ i, μ.real (A i ∩ Good) * c i := by
        simp only [cost, Set.indicator, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => hsingle i)
      _ ≤ ∑ i, (b i * μ.real Good) * c i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hGood).mp (hprob i)) (hc i)
      _ = (∑ i, b i * c i) * μ.real Good := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by ring)
  obtain ⟨ω, hω, hmin⟩ := Finset.exists_min_image S cost hS
  have hlower : cost ω * μ.real Good ≤ ∑ η ∈ S, μ.real {η} * cost η := by
    rw [← hmass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro η hη
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hmin η hη) (measureReal_nonneg)
  exact ⟨ω, (Finset.mem_filter.mp hω).2,
    (mul_le_mul_iff_of_pos_right hGood).mp (hlower.trans hsum)⟩

theorem exists_conditional_mark_budget {E : Type*} [Fintype E] [DecidableEq E]
    (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (Good : Set (E → Bool))
    (hGood : 0 < (bitProductMeasure E p hp₀ hp₁).real Good)
    (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) (r : ℝ)
    (hmark : ∀ e, (bitProductMeasure E p hp₀ hp₁).real
      (fixedBits {e} true ∩ Good) / (bitProductMeasure E p hp₀ hp₁).real Good ≤ r) :
    ∃ ω ∈ Good, (∑ e, if ω e = true then c e else 0) ≤ r * ∑ e, c e := by
  classical
  obtain ⟨ω, hω, hcost⟩ := exists_conditional_cost_le
    (bitProductMeasure E p hp₀ hp₁) Good hGood
    (fun e => fixedBits {e} true) c (fun _ => r) hc hmark
  refine ⟨ω, hω, ?_⟩
  simpa only [Set.indicator, fixedBits, Set.mem_ofPred_eq, Finset.mem_singleton, forall_eq,
    ← Finset.mul_sum] using hcost

end Erdos911
