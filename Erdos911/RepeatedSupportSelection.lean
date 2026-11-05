import Erdos911.RepeatedTypeParameters

namespace Erdos911

/-- Quantitative repeated-type pruning. A fixed component type survives
with small bad-copy support once the two available-edge logarithms meet
the displayed bounds. -/
theorem exists_repeated_type_with_small_support {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (P : Finset (RectangleBlock W)) (R : ℕ) (hP : BoundedEdgeBlocks P R)
    (A d k a D M : ℕ) (Λ : ℝ)
    (hscale : 32768 * A ≤ d) (hlog : 32768 ≤ Real.log d)
    (ha : 65536 ≤ a) (haverage : d * k ≤ 2 * a)
    (hD : ∀ w, H.degree w ≤ D) (hDpos : 1 ≤ D) (hDpow : D ≤ d ^ A)
    (hM : ∀ S : Finset W, S.card = k → (H.induce (S : Set W)).edgeSet.ncard ≤ M)
    (hMpos : 0 < M) (hR : 0 < R) (hΛ : 0 < Λ) (hΛd : Λ ≤ d)
    (hsize : Real.log ((M : ℝ) / a) ≤ (1 + 1 / 8192 : ℝ) * Real.log d)
    (hpair : (1 - 1 / 8192 : ℝ) * Real.log d ≤ Real.log ((M : ℝ) / ((a : ℝ) * R)))
    (hclass : Real.exp ((1 - 1 / 32768 : ℝ) * a * Real.log d) ≤
      ((componentClass G k a).card : ℝ)) :
    ∃ t ∈ componentClass G k a,
      ((repeatedBadSupport G H P (a / 1024) t).card : ℝ) ≤ H.edgeFinset.card / (16 * Λ) ∧
      ∀ f : (componentModel G t).Copy
          (H.deleteEdges (repeatedBadSupport G H P (a / 1024) t : Set (Sym2 W))),
        repeatedEdgeVolume P (copyRawEdges
          ((SimpleGraph.Copy.ofLE _ H (H.deleteEdges_le _)).comp f)) < 3 * (a / 1024) := by
  have hthreshold := repeated_threshold_bounds a ha
  have hroot := polynomial_repeated_root_bound A d k a D hscale (by linarith)
    haverage hDpos hDpow
  have hexponent := repeated_type_exponent_deficit k a (a / 1024) D M R d hlog
    hroot hsize hpair hthreshold.2
  let L := (1 - 1 / 32768 : ℝ) * Real.log d
  have hgap : repeatedTypeExponent k a (a / 1024) D M R ≤ L * a + Real.log (1 / (16 * Λ)) :=
    repeated_type_support_log_gap d Λ L (repeatedTypeExponent k a (a / 1024) D M R) a
      hlog hΛ hΛd ha le_rfl hexponent
  have hclass' : Real.exp (L * a) ≤ ((componentClass G k a).card : ℝ) := by
    simpa only [L, mul_assoc, mul_comm, mul_left_comm] using hclass
  obtain ⟨t, ht, hsupport⟩ := exists_repeated_type_support_of_gap G H P R hP k a (a / 1024) D M
    hD hM (by omega) hMpos hR hthreshold.1 L (1 / (16 * Λ)) (by positivity) hclass' hgap
  refine ⟨t, ht, ?_, ?_⟩
  · calc
      ((repeatedBadSupport G H P (a / 1024) t).card : ℝ) ≤
          (1 / (16 * Λ)) * H.edgeFinset.card := hsupport
      _ = _ := by ring
  · have hsizeT : componentSize G t = a := (Finset.mem_filter.mp ht).2.2
    have hpositive : 0 < componentSize G t := by omega
    intro f
    exact Nat.lt_of_not_ge (repeatedBadSupport_eliminates_bad_copies G H P (a / 1024) t hpositive f)

end Erdos911
