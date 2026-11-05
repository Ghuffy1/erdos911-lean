import Erdos911.EdgeColorings
import Erdos911.ForestEntropy
import Erdos911.CubeMeasure

open MeasureTheory

namespace Erdos911

noncomputable def fairBitMeasure (E : Type*) [Fintype E] : Measure (E → Bool) :=
  Measure.pi (fun _ => bernoulliMarginal (1 / 2) (by norm_num) (by norm_num))

instance fairBitMeasure_isProbabilityMeasure (E : Type*) [Fintype E] :
    IsProbabilityMeasure (fairBitMeasure E) := by
  unfold fairBitMeasure
  infer_instance

theorem fairBitMeasure_fixed_coordinates {E : Type*} [Fintype E] [DecidableEq E]
    (D : Finset E) (b : Bool) :
    (fairBitMeasure E).real {ω | ∀ e ∈ D, ω e = b} = (1 / 2 : ℝ) ^ D.card := by
  classical
  have hset : {ω : E → Bool | ∀ e ∈ D, ω e = b} =
      Set.univ.pi (fun e => if e ∈ D then ({b} : Set Bool) else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro h e
      by_cases he : e ∈ D
      · simpa only [ite_eq_left he, Set.mem_singleton_iff] using h e he
      · simp only [ite_eq_right he, Set.mem_univ]
    · intro h e he
      simpa only [ite_eq_left he, Set.mem_singleton_iff] using h e
  calc
    (fairBitMeasure E).real {ω | ∀ e ∈ D, ω e = b} =
        ∏ e : E, (bernoulliMarginal (1 / 2) (by norm_num) (by norm_num)).real
          (if e ∈ D then {b} else Set.univ) := by
      simp only [Measure.real, fairBitMeasure, hset, Measure.pi_pi, ENNReal.toReal_prod]
    _ = ∏ e : E, if e ∈ D then (1 / 2 : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ D
      · simp only [ite_eq_left he, bernoulliMarginal_real_singleton]
        cases b <;> norm_num [bernoulliWeight]
      · simp only [ite_eq_right he, probReal_univ]
    _ = (1 / 2 : ℝ) ^ D.card := by
      rw [Finset.prod_ite_mem_eq, Finset.prod_const]

/-- The finite first-moment argument for avoiding monochromatic members of
a uniform set family. -/
theorem exists_nonmonochromatic_coloring {E I : Type*} [Fintype E] [DecidableEq E]
    [Fintype I] (D : I → Finset E) (r : ℕ) (hcard : ∀ i, (D i).card = r)
    (hbudget : (2 * Fintype.card I : ℝ) * (1 / 2 : ℝ) ^ r < 1) :
    ∃ ω : E → Bool, ∀ i b, ¬ ∀ e ∈ D i, ω e = b := by
  classical
  let A : I × Bool → Set (E → Bool) := fun p => {ω | ∀ e ∈ D p.1, ω e = p.2}
  have hsum : (∑ p : I × Bool, (fairBitMeasure E).real (A p)) < 1 := by
    calc
      (∑ p : I × Bool, (fairBitMeasure E).real (A p)) =
          (2 * Fintype.card I : ℝ) * (1 / 2 : ℝ) ^ r := by
        simp only [A, fairBitMeasure_fixed_coordinates, hcard, Finset.sum_const,
          Finset.card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul,
          Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ < 1 := hbudget
  have hnotuniv : (⋃ p, A p) ≠ Set.univ := by
    intro h
    have hle := measureReal_iUnion_fintype_le (μ := fairBitMeasure E) A
    rw [h, probReal_univ] at hle
    exact (not_lt_of_ge hle) hsum
  have hex : ∃ ω, ω ∉ ⋃ p, A p := by
    by_contra h
    push Not at h
    exact hnotuniv (Set.eq_univ_of_forall h)
  obtain ⟨ω, hω⟩ := hex
  exact ⟨ω, fun i b h => hω (Set.mem_iUnion.mpr ⟨(i, b), h⟩)⟩

theorem edgeColorClass_free_of_no_monochrome {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (ω : H.edgeSet → Bool) (b : Bool)
    (hω : ∀ f : G.Copy H, ¬ ∀ e ∈ copyHostEdges f, ω e = b) :
    ¬G.IsContained (edgeColorClass H ω b) := by
  rintro ⟨f⟩
  exact hω ((SimpleGraph.Copy.ofLE _ _ (edgeColorClass_le H ω b)).comp f)
    (colored_copyHostEdges H ω b f)

/-- A first-moment criterion stated with ordinary, unlabelled subgraph
copies and yielding the two-color obstruction used by `sizeRamsey`. -/
theorem exists_avoiding_coloring_of_copyCount {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hbudget : (2 * H.copyCount G : ℝ) * (1 / 2 : ℝ) ^ G.edgeFinset.card < 1) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  classical
  let I : Finset (Finset H.edgeSet) :=
    (Finset.univ : Finset (G.Copy H)).image copyHostEdges
  have hcard : ∀ s : I, s.val.card = G.edgeFinset.card := by
    intro s
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp s.property
    rw [← hf]
    exact copyHostEdges_card G f
  have hbudgetI : (2 * Fintype.card I : ℝ) * (1 / 2 : ℝ) ^ G.edgeFinset.card < 1 := by
    have hI : (Fintype.card I : ℝ) ≤ H.copyCount G := by
      rw [Fintype.card_coe]
      exact_mod_cast copyHostEdges_image_card_le G H
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hI (by norm_num)) (by positivity)) hbudget
  obtain ⟨ω, hω⟩ := exists_nonmonochromatic_coloring
    (fun s : I => s.val) G.edgeFinset.card hcard hbudgetI
  have hfree : ∀ b, ¬G.IsContained (edgeColorClass H ω b) := by
    intro b
    apply edgeColorClass_free_of_no_monochrome G H ω b
    intro f
    exact hω ⟨copyHostEdges f, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩ b
  refine ⟨edgeColorClass H ω false, edgeColorClass_le H ω false, hfree false, ?_⟩
  rw [edgeColorClass_complement]
  exact hfree true

/-- The spanning-forest first-moment criterion, including the factorial
divisor for every repeated component type. -/
theorem forest_first_moment_coloring {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (D : ℕ)
    (hD : ∀ v, G.degree v ≤ D)
    (hneighbors : ∀ v, ∃ w, G.Adj v w) (hedge : ∃ u v, G.Adj u v)
    (hbudget :
      2 * (((2 * H.edgeFinset.card : ℝ) ^ Nat.card G.ConnectedComponent *
        ((2 * H.edgeFinset.card : ℝ) /
          ((Fintype.card V - Nat.card G.ConnectedComponent : ℕ) : ℝ)) ^
          (Fintype.card V - Nat.card G.ConnectedComponent) *
            (D : ℝ) ^ (Fintype.card V - Nat.card G.ConnectedComponent)) /
              (∏ t : ComponentType G, ((componentMultiplicity G t).factorial : ℝ))) *
        (1 / 2 : ℝ) ^ G.edgeFinset.card < 1) :
    ∃ R : SimpleGraph W, R ≤ H ∧ ¬G.IsContained R ∧ ¬G.IsContained (H \ R) := by
  apply exists_avoiding_coloring_of_copyCount G H
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (graph_forest_component_bound G H D hD hneighbors hedge) (by norm_num))
      (by positivity)) hbudget

end Erdos911
