import NeuralNetwork.ThreeD.BoltzmannLearning.Core
import NeuralNetwork.ThreeD.BoltzmannLearning.FiniteGibbs
import NeuralNetwork.ThreeD.BoltzmannLearning.VectorGibbs
import NeuralNetwork.ThreeD.BoltzmannLearning.VectorGibbsLearning
import NeuralNetwork.ThreeD.BoltzmannLearning.SymmetricBinaryInstantiation
import NeuralNetwork.ThreeD.BoltzmannLearning.SymmetricBinaryLearning
import NeuralNetwork.ThreeD.BoltzmannLearning.SymmetricBinaryLearningRule
import NeuralNetwork.ThreeD.BoltzmannLearning.TwoStateBridge
import NeuralNetwork.ThreeD.BoltzmannLearning.OptlibBridge

/-!
## ThreeD Boltzmann Machine Learning: SOTA entrypoint

This is the import surface for integrating `NeuralNetwork/NeuralNetwork/BMLearning.md` ideas
into the unified ThreeD vocabulary.

Current status:
- core definitions are in `BoltzmannLearning.Core`
- TwoState bridge is in `BoltzmannLearning.TwoStateBridge`
- Optlib hook is in `BoltzmannLearning.OptlibBridge`
- next: prove the classic “positive phase minus negative phase” rule as an actual gradient theorem
  for an explicit exponential-family/Gibbs model on finite configurations, then lift to
  Georgii/DLR specifications on infinite lattices.
-/
