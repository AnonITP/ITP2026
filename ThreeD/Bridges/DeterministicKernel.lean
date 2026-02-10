import ThreeD.Core
import ThreeD.Invariant
import Mathlib.Probability.Kernel.Basic

/-!
## Bridge: deterministic maps as kernels

This is a key unification step: once `f : X → X` is turned into the deterministic kernel
`Kernel.deterministic f`, all of the kernel-level invariance / composition lemmas apply equally
to deterministic dynamics (MCNN schedules) and stochastic dynamics (MCMC, Gibbs specifications).
-/

namespace NeuralNetwork

namespace ThreeD

namespace Bridges

open ProbabilityTheory MeasureTheory

section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Deterministic map as a kernel: `x ↦ δ_{f(x)}`. -/
noncomputable def deterministicKernel (f : X → Y) (hf : Measurable f) : Kernel X Y :=
  ProbabilityTheory.Kernel.deterministic f hf

end

section

variable {Θ X : Type*} [MeasurableSpace X]

/-- Lift deterministic dynamics into stochastic dynamics via Dirac kernels. -/
noncomputable def dynamicsToStochastic
    (D : ThreeD.DeterministicDynamics Θ X) (hstep : ∀ θ, Measurable (D.step θ)) :
    ThreeD.StochasticDynamics Θ X where
  K := fun θ => deterministicKernel (X := X) (Y := X) (D.step θ) (hstep θ)

end

end Bridges

end ThreeD

end NeuralNetwork
