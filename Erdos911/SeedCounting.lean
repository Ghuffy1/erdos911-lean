import Erdos911.RootedCounting
import Mathlib.Data.Fintype.Powerset

namespace Erdos911

theorem rooted_seed_properties {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (s : ℕ)
    (S : rootedConnectedSetsAtMost G root s) :
    root ∈ S.val ∧ S.val.card ≤ s ∧ (G.induce (S.val : Set V)).Connected := by
  classical
  exact (Finset.mem_filter.mp S.property).2

def rootedSeedRoot {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (root : V) (s : ℕ)
    (S : rootedConnectedSetsAtMost G root s) : (S.val : Set V) :=
  ⟨root, (rooted_seed_properties G root s S).1⟩

/-- The seed records its connected target vertex set, a rooted host map,
and the subset of vertices flagged by the original random sample. -/
abbrev RootedSeedConfiguration {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (root : V) (image : W) (s : ℕ) :=
  Σ S : rootedConnectedSetsAtMost G root s,
    {f : (G.induce (S.val : Set V)) →g H // f (rootedSeedRoot G root s S) = image} ×
      Finset (S.val : Set V)

theorem rooted_seed_configuration_count {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (Δ D : ℕ)
    (hΔ : ∀ v, G.degree v ≤ Δ) (hD : ∀ w, H.degree w ≤ D)
    (hΔpos : 1 ≤ Δ) (hDpos : 1 ≤ D) (root : V) (image : W) (s : ℕ) :
    Fintype.card (RootedSeedConfiguration G H root image s) ≤
      (s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s := by
  classical
  have hfiber : ∀ S : rootedConnectedSetsAtMost G root s,
      Fintype.card ({f : (G.induce (S.val : Set V)) →g H //
        f (rootedSeedRoot G root s S) = image} × Finset (S.val : Set V)) ≤
        D ^ (2 * s) * 2 ^ s := by
    intro S
    have hS := rooted_seed_properties G root s S
    have horder : Fintype.card (S.val : Set V) = S.val.card := by simp
    have hhom := rooted_homomorphism_count (G.induce (S.val : Set V)) H hS.2.2
      D hD (rootedSeedRoot G root s S) image
    have hhom' : Fintype.card {f : (G.induce (S.val : Set V)) →g H //
        f (rootedSeedRoot G root s S) = image} ≤ D ^ (2 * s) := by
      apply hhom.trans
      rw [horder]
      exact pow_le_pow_right₀ hDpos (by omega)
    have hflags : Fintype.card (Finset (S.val : Set V)) ≤ 2 ^ s := by
      rw [Fintype.card_finset, horder]
      exact pow_le_pow_right₀ (by decide) hS.2.1
    rw [Fintype.card_prod]
    exact Nat.mul_le_mul hhom' hflags
  unfold RootedSeedConfiguration
  rw [Fintype.card_sigma]
  calc
    (∑ S : rootedConnectedSetsAtMost G root s,
        Fintype.card ({f : (G.induce (S.val : Set V)) →g H //
          f (rootedSeedRoot G root s S) = image} × Finset (S.val : Set V))) ≤
        ∑ _S : rootedConnectedSetsAtMost G root s, D ^ (2 * s) * 2 ^ s :=
      Finset.sum_le_sum (fun S _ => hfiber S)
    _ = (rootedConnectedSetsAtMost G root s).card * (D ^ (2 * s) * 2 ^ s) := by simp
    _ ≤ ((s + 1) * Δ ^ (2 * s)) * (D ^ (2 * s) * 2 ^ s) :=
      Nat.mul_le_mul_right _ (rooted_connected_sets_at_most_count G Δ hΔ hΔpos root s)
    _ = (s + 1) * Δ ^ (2 * s) * D ^ (2 * s) * 2 ^ s := by ac_rfl

end Erdos911
