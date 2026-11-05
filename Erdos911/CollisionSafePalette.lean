import Erdos911.SparseCollisionLabels
import Erdos911.FiniteDegreeColoring

namespace Erdos911

abbrev CollisionPalette (D K k : ℕ) :=
  Fin (max 1 (K * (D + 1) ^ (12 * k))) × Fin (D * (D + 1) + 1)

theorem collisionPalette_card (D K k : ℕ) : Fintype.card (CollisionPalette D K k) =
    max 1 (K * (D + 1) ^ (12 * k)) * (D * (D + 1) + 1) := by simp [CollisionPalette]

/-- Append a proper two-step coloring to the random labels. This makes
labels injective on every neighborhood without increasing label collisions. -/
theorem exists_collision_safe_palette {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D K k : ℕ)
    (hD : 2 ≤ D) (hk : 2 ≤ k) (hmax : ∀ v, G.degree v ≤ D) :
    ∃ f : V → CollisionPalette D K k,
      (∀ u v, G.Adj u v → f u ≠ f v) ∧
      (∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w) ∧
      (∀ S : Finset V, S.card ≤ K → (G.induce (S : Set V)).Connected →
        k * (repeatedVertices S f).card ≤ 2 * S.card) := by
  let A := Fin (max 1 (K * (D + 1) ^ (12 * k)))
  have hA : 0 < max 1 (K * (D + 1) ^ (12 * k)) := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  let : Nonempty A := ⟨⟨0, hA⟩⟩
  obtain ⟨a, ha⟩ := exists_sparse_collision_labeling (A := A) G D K k hD hk hmax
    (by simpa only [A, Fintype.card_fin] using (le_max_right 1 (K * (D + 1) ^ (12 * k))))
  obtain ⟨c, hc, hneighborhood⟩ := exists_two_step_coloring G D hmax
  let f : V → CollisionPalette D K k := fun v => (a v, c v)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro u v huv heq
    exact hc u v huv (congrArg Prod.snd heq)
  · intro u v w huv huw heq
    exact hneighborhood u v w huv huw (congrArg Prod.snd heq)
  · intro S hS hconn
    have hsub : repeatedVertices S f ⊆ repeatedVertices S a := by
      intro v hv
      obtain ⟨hvS, w, hwS, hwv, heq⟩ := (mem_repeatedVertices S f v).mp hv
      exact (mem_repeatedVertices S a v).mpr ⟨hvS, w, hwS, hwv, congrArg Prod.fst heq⟩
    exact (Nat.mul_le_mul_left k (Finset.card_le_card hsub)).trans (ha S hS hconn)

end Erdos911
