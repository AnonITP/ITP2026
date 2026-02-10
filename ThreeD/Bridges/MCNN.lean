import ThreeD.Core
import MCNN.EnergyLens
import MCNN.MarkovSemantics

/-!
## Bridge: MCNN → ThreeD

This file provides lightweight coercions:

- `MCNN.EnergyLens` (energy + certified gradient) gives a `ThreeD.EnergyModel`.
- `MCNN.MarkovSemantics.Step` is already the right categorical “step” object; we expose it as a
  `ThreeD`-named alias for use in the unified entrypoint.

We intentionally keep this layer minimal; deeper bridges (e.g. kernels, Langevin/HMC, etc.)
will live in separate files.
-/

namespace NeuralNetwork

namespace ThreeD

namespace Bridges

namespace MCNN

/-- Forget the gradient and view an `MCNN.EnergyLens` as an unparameterized `ThreeD.EnergyModel`. -/
def energyModelOfEnergyLens
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : _root_.MCNN.EnergyLens H) : ThreeD.EnergyModel H :=
  ⟨L.energy⟩

/-!
### Categorical step alias

This is just a naming bridge: the underlying notion is already the same.
-/

universe v u

/-- Naming bridge for the categorical step object used with Markov semantics. -/
abbrev MarkovStep {C : Type u} [CategoryTheory.Category.{v} C] (X : C) :=
  _root_.MCNN.MarkovSemantics.Step (C := C) X

end MCNN

end Bridges

end ThreeD

end NeuralNetwork
