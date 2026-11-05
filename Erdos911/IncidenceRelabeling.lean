import Erdos911.IncidencePrunedColoring
import Erdos911.NearRegularComponentColoring

namespace Erdos911

theorem copyHighNeighbors_card_comp_iso {U V W : Type*}
    [Fintype U] [Fintype V] [Fintype W]
    {F : SimpleGraph U} {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel F.Adj] [DecidableRel G.Adj]
    (f : G.Copy H) (e : F ≃g G) (high : Finset W) (v : U) :
    (copyHighNeighbors F (f.comp e.toCopy) high v).card =
      (copyHighNeighbors G f high (e v)).card := by
  classical
  apply Finset.card_bij (fun u _ => e u)
  · intro u hu
    obtain ⟨hvu, hhigh⟩ := (mem_copyHighNeighbors F (f.comp e.toCopy) high v u).mp hu
    exact (mem_copyHighNeighbors G f high (e v) (e u)).mpr ⟨e.map_rel_iff.mpr hvu, hhigh⟩
  · intro u _ w _ h
    exact e.injective h
  · intro w hw
    obtain ⟨hvw, hhigh⟩ := (mem_copyHighNeighbors G f high (e v) w).mp hw
    refine ⟨e.symm w, ?_, by simp⟩
    apply (mem_copyHighNeighbors F (f.comp e.toCopy) high v (e.symm w)).mpr
    exact ⟨e.map_rel_iff.mp (by simpa only [e.apply_symm_apply] using hvw),
      by change f (e (e.symm w)) ∈ high; simpa only [e.apply_symm_apply] using hhigh⟩

theorem incidenceOrientationDefects_card_comp_iso {U V W : Type*}
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] [Fintype W]
    (F : SimpleGraph U) [DecidableRel F.Adj] (G : SimpleGraph V) [DecidableRel G.Adj]
    {H : SimpleGraph W} (f : G.Copy H) (e : F ≃g G) (right : Finset U) (high : Finset W) (d : ℕ) :
    (incidenceOrientationDefects F (f.comp e.toCopy) right high d).card =
      (incidenceOrientationDefects G f (right.image e) high d).card := by
  classical
  apply Finset.card_bij (fun v _ => e v)
  · intro v hv
    obtain ⟨hvr, hvbad⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨v, hvr, rfl⟩, ?_⟩
    rw [← copyHighNeighbors_card_comp_iso f e high v]
    exact hvbad
  · intro u _ v _ h
    exact e.injective h
  · intro w hw
    obtain ⟨hwr, hwbad⟩ := Finset.mem_filter.mp hw
    obtain ⟨v, hvr, rfl⟩ := Finset.mem_image.mp hwr
    refine ⟨v, Finset.mem_filter.mpr ⟨hvr, ?_⟩, rfl⟩
    rw [copyHighNeighbors_card_comp_iso f e high v]
    exact hwbad

end Erdos911
