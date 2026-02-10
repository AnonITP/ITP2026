import ThreeD.BoltzmannLearning.VectorGibbsLearning
import ThreeD.BoltzmannLearning.TwoStateBridge
import HopfieldNet.Quiver.BM.BoltzmannMachine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block

/-!
## Concrete instantiation: SymmetricBinary Hopfield energy as a vector-parameter Gibbs model

This file connects the existing concrete Hopfield Hamiltonian
`HopfieldNet.Quiver.BM.BoltzmannMachine.HopfieldEnergy.hamiltonian`
to the abstract finite vector-parameter Gibbs theorem layer:

- `VectorGibbs` / `VectorGibbsLearning`.

The key point is to exhibit an explicit sufficient-statistic map `stat` and a parameter vector
`θ` such that the Hamiltonian is *exactly* `-⟪stat x, θ⟫`, hence learning gradients become
“data statistic − model statistic” without any extra axioms.
-/

namespace NeuralNetwork
namespace ThreeD
namespace BoltzmannLearning

open scoped BigOperators
open InnerProductSpace
open Matrix

namespace SymmetricBinaryInstantiation

noncomputable section

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

/-
We import `HopfieldNet.Quiver.BM.BoltzmannMachine` , and we use its
canonical SymmetricBinary Hopfield Hamiltonian `HopfieldEnergy.hamiltonian`.

To apply `VectorGibbs`/`VectorGibbsLearning`, we package parameters into a finite-dimensional
Hilbert space `Θ := EuclideanSpace ℝ (U × U ⊕ U)` and define a sufficient statistic
`stat : (Config U) → Θ` so that:

`HopfieldEnergy.hamiltonian p (stateOfConfig c) = -⟪stat c, thetaOfParams p⟫`.
-/

open TwoState

abbrev NN : NeuralNetwork ℝ U ℝ := TwoState.SymmetricBinary ℝ U

instance : TwoStateNeuralNetwork (NN := (NN (U := U))) :=
  TwoState.instTwoStateSymmetricBinary (R := ℝ) (U := U)

/-- The spin value associated to a Bool config, expressed using the distinguished TwoState
activations (so this lemma does not depend on a particular `{±1}` convention). -/
def spin (c : Config U) (u : U) : ℝ :=
  cond (c u) (TwoStateNeuralNetwork.σ_pos (NN := (NN (U := U))))
    (TwoStateNeuralNetwork.σ_neg (NN := (NN (U := U))))

abbrev Θ (U : Type) := EuclideanSpace ℝ (U × U ⊕ U)

noncomputable def stat (c : Config U) : Θ U :=
  WithLp.toLp 2 (V := (U × U ⊕ U) → ℝ) fun
    | Sum.inl (i, j) => (1 / 2 : ℝ) * spin (U := U) c i * spin (U := U) c j
    | Sum.inr i      => - spin (U := U) c i

noncomputable def thetaOfParams (p : _root_.Params (NN (U := U))) : Θ U :=
  WithLp.toLp 2 (V := (U × U ⊕ U) → ℝ) fun
    | Sum.inl (i, j) => p.w i j
    | Sum.inr i      => (p.θ i).get fin0

noncomputable def stateOfConfig (c : Config U) : (NN (U := U)).State :=
  TwoStateBridge.stateOfConfig (NN := (NN (U := U))) c

theorem hamiltonian_eq_vectorGibbs_energy
    (p : _root_.Params (NN (U := U))) (c : Config U) :
    HopfieldEnergy.hamiltonian (R := ℝ) (U := U) p (stateOfConfig (U := U) c)
      =
    VectorGibbs.energy (X := Config U) (Θ := Θ U) (stat := stat (U := U)) (thetaOfParams (U := U) p) c := by
  classical
  unfold HopfieldEnergy.hamiltonian
  have hact : (stateOfConfig (U := U) c).act = spin (U := U) c := by
    funext u
    by_cases hc : c u <;> simp [stateOfConfig, TwoStateBridge.stateOfConfig, spin, hc]
  -- The key identity used for the RHS is `EuclideanSpace.inner_toLp_toLp`.
  simp [VectorGibbs.energy, stat, thetaOfParams, hact, spin, NN, TwoState.fin0,
    EuclideanSpace.inner_toLp_toLp, Matrix.dotProduct_block]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
  simp [spin, NN, mul_assoc, mul_left_comm, mul_comm, add_comm]

end

end SymmetricBinaryInstantiation

end BoltzmannLearning
end ThreeD
end NeuralNetwork
