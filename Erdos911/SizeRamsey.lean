/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

/-!
The definition below is copied verbatim from the Formal Conjectures utility
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SizeRamsey.lean`.
It does not import any conjecture or its placeholder proof.
-/

namespace SimpleGraph

noncomputable def sizeRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { m | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
    F.edgeSet.ncard = m ∧
    ∀ (R : SimpleGraph (Fin n)), R ≤ F →
      G.IsContained R ∨ H.IsContained (F \ R) }

end SimpleGraph
