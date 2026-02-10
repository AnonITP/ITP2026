import NeuralNetwork.ThreeD.SOTA
import NeuralNetwork.ThreeD.Bridges.GibbsMeasure
import NeuralNetwork.ThreeD.Bridges.GibbsPotential
import NeuralNetwork.ThreeD.Invariant

/-!
## ThreeD + GibbsMeasure entrypoint

This is the “foundational / infinite lattice” extension of `NeuralNetwork.ThreeD.SOTA`:

- the ThreeD core vocabulary + MCNN/MCMC bridges
- plus the Georgii/DLR `GibbsMeasure.Specification` bridge (indexed kernels `γ(Λ)` on `S → E`)
- plus the general “potential → specification → indexed kernels” bridge (`GibbsPotential`)
-/
