import NeuralNetwork.ThreeD.Bridges.GibbsMeasure
import GibbsMeasure.Potential

/-!
## Bridge: interacting potentials → Gibbs specifications → ThreeD indexed stochastic dynamics

For infinite-lattice foundations, the most stable path is:

`Potential Φ`  →  `Potential.gibbsSpecification Φ β ν`  →  `ThreeD.IndexedStochasticDynamics`

This file bundles that pipeline so that any finitary measurable interaction can be used as a
ThreeD-local-update kernel family indexed by finite volumes `Λ : Finset S`.
-/

namespace NeuralNetwork

namespace ThreeD

namespace Bridges

namespace GibbsPotential

open MeasureTheory

variable {S E : Type*} [MeasurableSpace E]
variable [DecidableEq S]

variable (Φ : _root_.Potential S E) [_root_.Potential.IsFinitary Φ] [_root_.Potential.IsPotential Φ]

/-- ThreeD indexed stochastic dynamics induced by an interacting potential via the Gibbs specification. -/
noncomputable def gibbsDynamics
    (β : ℝ) (ν : Measure E) [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      Specification.premodifierZ ν (_root_.Potential.boltzmannWeight (Φ := Φ) β) Λ η ≠ ⊤) :
    ThreeD.IndexedStochasticDynamics (Finset S) PUnit (S → E) :=
  Bridges.GibbsMeasure.toIndexedStochasticDynamics
    (S := S) (E := E) (_root_.Potential.gibbsSpecification (Φ := Φ) β ν hZ)

end GibbsPotential

end Bridges

end ThreeD

end NeuralNetwork
