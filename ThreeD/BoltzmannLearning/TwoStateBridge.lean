import ThreeD.BoltzmannLearning.Core
import HopfieldNet.Quiver.NN.TwoState

/-!
## Bridge: `NeuralNetwork.NeuralNetwork.TwoState` → `ThreeD.BoltzmannLearning`

`TwoState.lean` already provides:

- a general two-state NN interface (`TwoStateNeuralNetwork`)
- a one-site Gibbs update `gibbsUpdate` and sweeps `gibbsSweep`
- an energy abstraction `EnergySpec'` with the fundamental flip/energy relation

This file connects that work to the BM-learning vocabulary by:

- interpreting a Bool-configuration `U → Bool` as a `NN.State` using `σ_pos`/`σ_neg`
- using `EnergySpec'.E` (pushed along `f : R →+* ℝ`) as an energy on Bool-configurations

-/

namespace NeuralNetwork

namespace ThreeD

namespace BoltzmannLearning

namespace TwoStateBridge

open NeuralNetwork

universe uR uU uσ

variable {R U σ: Type} --{U : Type uU} {σ : Type uσ}

section

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [DecidableEq U]
variable {NN : NeuralNetwork R U σ} [TwoStateNeuralNetwork (NN := NN)]

/-- Build a TwoState `NN.State` from a Bool-config by choosing `σ_pos`/`σ_neg` pointwise. -/
noncomputable def stateOfConfig (c : BoltzmannLearning.Config U) : NN.State :=
{ act := fun u => cond (c u) (TwoStateNeuralNetwork.σ_pos (NN := NN)) (TwoStateNeuralNetwork.σ_neg (NN := NN))
  hp := by
    intro u
    by_cases h : c u
    · simp [h, TwoStateNeuralNetwork.h_pact_pos (NN := NN)]
    · simp [h, TwoStateNeuralNetwork.h_pact_neg (NN := NN)] }

/-- Push an `EnergySpec'` to an energy on Bool-configs via `stateOfConfig` and a ring hom `f`. -/
noncomputable def energyBool
    (E : TwoState.EnergySpec' (NN := NN)) (f : R →+* ℝ) (p : _root_.Params NN) :
    BoltzmannLearning.Config U → ℝ :=
  fun c => f (E.E p (stateOfConfig (NN := NN) c))

/-- Package the TwoState energy as a `BoltzmannLearning.BM` on Bool-configurations. -/
noncomputable def bmOfEnergySpec
    (E : TwoState.EnergySpec' (NN := NN)) (f : R →+* ℝ) :
    BoltzmannLearning.BM (_root_.Params NN) U :=
{ energy := fun p c => energyBool (NN := NN) E f p c }

end

end TwoStateBridge

end BoltzmannLearning

end ThreeD

end NeuralNetwork
