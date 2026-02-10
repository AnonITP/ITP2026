import ThreeD.Core
import MCMC.Finite.Core
import MCMC.Finite.toKernel

/-!
## Bridge: finite MCMC matrices → ThreeD stochastic dynamics

`MCMC/Finite/toKernel.lean` constructs a Markov kernel from a row-stochastic matrix:

- `MCMC.Finite.matrixToKernel : Matrix n n ℝ → IsStochastic P → Kernel n n`

This file packages that as a `ThreeD.StochasticDynamics` instance.
-/

namespace NeuralNetwork

namespace ThreeD

open ProbabilityTheory

namespace Bridges

namespace MCMCFinite

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
  [MeasurableSpace n] [MeasurableSingletonClass n]

/-- A row-stochastic matrix packaged with its certificate. -/
structure StochMatrix (n : Type*) [Fintype n] where
  P : Matrix n n ℝ
  hP : MCMC.Finite.IsStochastic P

/-- The induced Markov kernel on a finite state space. -/
noncomputable def StochMatrix.kernel (M : StochMatrix n) : Kernel n n :=
  MCMC.Finite.matrixToKernel (n := n) M.P M.hP

/-- View a finite stochastic matrix as ThreeD stochastic dynamics (no extra parameters). -/
noncomputable def toStochasticDynamics : ThreeD.StochasticDynamics (StochMatrix n) n where
  K := fun M => M.kernel

end MCMCFinite

end Bridges

end ThreeD

end NeuralNetwork
