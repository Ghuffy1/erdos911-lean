import Erdos911.PairMarkedRows
import Erdos911.IncidenceCodegrees
import Erdos911.CopyImages

namespace Erdos911

/-- Injective row maps cannot decrease common-neighbor counts. -/
theorem incidenceCodegree_le_of_maps {A B L R : Type*}
    [DecidableEq A] [Fintype B] [DecidableEq L] [Fintype R]
    (S : B → Finset A) (N : R → Finset L) (l : A → L) (r : B → R)
    (hr : Function.Injective r)
    (hmap : ∀ y x, x ∈ S y → l x ∈ N (r y)) (x z : A) :
    incidenceCodegree S x z ≤ incidenceCodegree N (l x) (l z) := by
  classical
  have hsub : (incidenceColumn S x ∩ incidenceColumn S z).image r ⊆
      incidenceColumn N (l x) ∩ incidenceColumn N (l z) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx, hz⟩ := Finset.mem_inter.mp hb
    have hxS : x ∈ S b := (Finset.mem_filter.mp hx).2
    have hzS : z ∈ S b := (Finset.mem_filter.mp hz).2
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap b x hxS⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmap b z hzS⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hr] at hcard
  exact hcard

theorem positive_incidenceCodegree_common_row {A B : Type*} [DecidableEq A] [Fintype B]
    (S : B → Finset A) (x z : A) (h : 0 < incidenceCodegree S x z) :
    ∃ y, x ∈ S y ∧ z ∈ S y := by
  classical
  obtain ⟨y, hy⟩ := Finset.card_pos.mp h
  obtain ⟨hx, hz⟩ := Finset.mem_inter.mp hy
  exact ⟨y, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hz).2⟩

/-- A red incidence embedding induces an unmarked copy of every pair
pattern supported by a positive target codegree threshold. -/
theorem red_incidence_induces_unmarked_pair_copy {V A B L R : Type*}
    [Fintype V] [DecidableEq A] [Fintype B] [Fintype L] [DecidableEq L] [Fintype R]
    (F : SimpleGraph V) (S : B → Finset A) (N : R → Finset L)
    (φ : V → A) (hφ : Function.Injective φ) (l : A → L) (hl : Function.Injective l)
    (r : B → R) (hr : Function.Injective r) (t : ℕ) (ht : 0 < t)
    (htarget : ∀ u v, F.Adj u v → t ≤ incidenceCodegree S (φ u) (φ v))
    (ω : Sym2 L → Bool)
    (hred : ∀ y x, x ∈ S y → l x ∈ pairRedRow (N (r y)) ω) :
    ∃ f : F.Copy (heavyIncidenceGraph N (t : ℝ)), ω ∈ fixedBits (copyRawEdges f) false := by
  classical
  have hmap (y : B) (x : A) (hx : x ∈ S y) : l x ∈ N (r y) :=
    (Finset.mem_sdiff.mp (hred y x hx)).1
  have hcode (u v : V) (huv : F.Adj u v) :
      t ≤ incidenceCodegree N (l (φ u)) (l (φ v)) :=
    (htarget u v huv).trans (incidenceCodegree_le_of_maps S N l r hr hmap (φ u) (φ v))
  let f : F.Copy (heavyIncidenceGraph N (t : ℝ)) := {
    toHom := {
      toFun := l ∘ φ
      map_rel' := fun {u v} huv => ⟨fun h => huv.ne (hφ (hl h)), by exact_mod_cast hcode u v huv⟩ }
    injective' := hl.comp hφ }
  refine ⟨f, ?_⟩
  intro e he
  obtain ⟨a, rfl⟩ := (mem_copyRawEdges_iff_exists f e).mp he
  rcases a with ⟨e, haEdge⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : F.Adj u v := haEdge
    have hpos : 0 < incidenceCodegree S (φ u) (φ v) := ht.trans_le (htarget u v huv)
    obtain ⟨y, hyu, hyv⟩ := positive_incidenceCodegree_common_row S (φ u) (φ v) hpos
    exact red_row_pair_unmarked (N (r y)) ω (l (φ u)) (l (φ v))
      (hred y (φ u) hyu) (hred y (φ v) hyv)

end Erdos911
