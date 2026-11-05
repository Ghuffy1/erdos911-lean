import Erdos911.TargetPatternGraph

namespace Erdos911

theorem mem_patternComponentRows {A R : Type*} [Fintype A]
    (T : R → Finset A) (B : Finset R) (P : SimpleGraph A) (c : P.ConnectedComponent) (y : R) :
    y ∈ patternComponentRows T B P c ↔ y ∈ B ∧ ∀ x ∈ T y, x ∈ c.supp := by
  classical
  exact Finset.mem_filter

end Erdos911
