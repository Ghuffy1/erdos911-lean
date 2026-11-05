import Erdos911.ProductCoordinates

open MeasureTheory

namespace Erdos911

def coordinateOverlapGraph {ι κ : Type*} (D : κ → Finset ι) : SimpleGraph κ where
  Adj i j := i ≠ j ∧ ¬Disjoint (D i) (D j)
  symm.symm _i _j h := ⟨h.1.symm, fun hd => h.2 hd.symm⟩
  loopless.irrefl _i h := h.1 rfl

instance {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (D : κ → Finset ι) :
    DecidableRel (coordinateOverlapGraph D).Adj := by
  unfold coordinateOverlapGraph
  infer_instance

theorem coordinateOverlapGraph_degree_le {ι κ : Type*} [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : κ → Finset ι) (a b : ℕ)
    (ha : ∀ i, (D i).card ≤ a)
    (hb : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ b) (i : κ) :
    (coordinateOverlapGraph D).degree i ≤ a * b := by
  classical
  have hsubset : (coordinateOverlapGraph D).neighborFinset i ⊆
      (D i).biUnion (fun j => Finset.univ.filter (fun k => j ∈ D k)) := by
    intro k hk
    have hdis : ¬Disjoint (D i) (D k) :=
      (((coordinateOverlapGraph D).mem_neighborFinset i k).mp hk).2
    obtain ⟨j, hj, hjk⟩ := Finset.not_disjoint_iff.mp hdis
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩⟩
  calc
    (coordinateOverlapGraph D).degree i =
        ((coordinateOverlapGraph D).neighborFinset i).card :=
      (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
    _ ≤ ((D i).biUnion (fun j => Finset.univ.filter (fun k => j ∈ D k))).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ j ∈ D i, (Finset.univ.filter (fun k => j ∈ D k)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ D i, b := Finset.sum_le_sum (fun j _ => hb j)
    _ = (D i).card * b := by simp
    _ ≤ a * b := Nat.mul_le_mul_right b (ha i)

/-- The symmetric local lemma for events with bounded coordinate support and
bounded incidence at each independent coordinate. -/
theorem exists_avoiding_coordinate_events {n m : ℕ} {β : Fin n → Type*}
    [∀ j, Fintype (β j)] [∀ j, MeasurableSpace (β j)]
    [∀ j, MeasurableSingletonClass (β j)]
    (μ : ∀ j, Measure (β j)) [∀ j, IsProbabilityMeasure (μ j)]
    (A : Fin m → Set (∀ j, β j)) (D : Fin m → Finset (Fin n))
    (hA : ∀ i, DependsOnlyOn (A i) (D i))
    (p : ℝ) (a b : ℕ)
    (hp : ∀ i, (Measure.pi μ).real (A i) ≤ p)
    (ha : ∀ i, (D i).card ≤ a)
    (hb : ∀ j, (Finset.univ.filter (fun i => j ∈ D i)).card ≤ b)
    (hc : Real.exp 1 * p * ((a * b : ℕ) + 1) ≤ 1) :
    ∃ ω, ∀ i, ω ∉ A i := by
  classical
  let Γ := coordinateOverlapGraph D
  have hΓ : ∀ i j, j ≠ i → ¬Γ.Adj i j → Disjoint (D i) (D j) := by
    intro i j hji hn
    by_contra hd
    exact hn ⟨hji.symm, hd⟩
  have hpos := LocalLemma.lll_symmetric (Measure.pi μ) A
    (fun i => (Set.toFinite (A i)).measurableSet) Γ
    (product_dependency_graph μ A D hA Γ hΓ) hp
    (coordinateOverlapGraph_degree_le D a b ha hb) hc
  have hnonempty : (⋂ i, (A i)ᶜ).Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    rw [he, measureReal_empty] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨ω, hω⟩ := hnonempty
  exact ⟨ω, by simpa only [Set.mem_iInter, Set.mem_compl_iff] using hω⟩

end Erdos911
