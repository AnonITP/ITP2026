import NeuralNetwork.NeuralNetwork.HopfieldGibbsBridge
import NeuralNetwork.NeuralNetwork.ComputableRealsBridge

/-!
## Demo: Hopfield random-scan Gibbs kernel is available

This is a minimal “smoke test” that the Hopfield `EnergySpec'` pipeline really exposes the
finite-state Gibbs API:
- one-site Gibbs update matrices
- random-scan Gibbs Markov matrix
- stochasticity (row-stochastic) proof via `PMFMatrix`.
-/

namespace NeuralNetwork

open scoped Temperature

namespace HopfieldGibbsDemo

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

-- The most direct specialization: scalar `R = ℝ`, and `f = id`.
example (p : Params (HopfieldNetwork ℝ U)) (T : Temperature) :
    MCMC.Finite.IsStochastic
      (HopfieldGibbsBridge.Boltz.randomScanMatrix (R := ℝ) (U := U) p T (RingHom.id ℝ)) := by
  simpa using
    (HopfieldGibbsBridge.Boltz.randomScanMatrix_isStochastic (R := ℝ) (U := U)
      (p := p) (T := T) (f := RingHom.id ℝ))

-- Same statement but using the abstract `HasToReal` map `toRealRingHom`.
example {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [NeuralNetwork.HasToReal R]
    (p : Params (HopfieldNetwork R U)) (T : Temperature) :
    MCMC.Finite.IsStochastic
      (HopfieldGibbsBridge.Boltz.randomScanMatrix (R := R) (U := U)
        p T (NeuralNetwork.HasToReal.toRealRingHom (R := R))) := by
  simpa using
    (HopfieldGibbsBridge.Boltz.randomScanMatrix_isStochastic (R := R) (U := U)
      (p := p) (T := T) (f := NeuralNetwork.HasToReal.toRealRingHom (R := R)))

end HopfieldGibbsDemo

end NeuralNetwork
