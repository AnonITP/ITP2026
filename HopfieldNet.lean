-- This module serves as the root of the `HopfieldNet` library.
-- Import modules here that should be built as part of the library.
import HopfieldNet.HN.aux
import HopfieldNet.NN
import HopfieldNet.HN.Core
import HopfieldNet.HN.Asym
import HopfieldNet.HN.test
--import HopfieldNet.HN.Test

import HopfieldNet.Stochastic
import HopfieldNet.DetailedBalance

import HopfieldNet.Mathematics.aux
import HopfieldNet.Mathematics.Analysis.CstarAlgebra.Classes
import HopfieldNet.Mathematics.Combinatorics.Quiver.Path
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.CollatzWielandt
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Defs
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Dominance
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Lemmas
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Primitive
import HopfieldNet.Mathematics.LinearAlgebra.Matrix.PerronFrobenius.Irreducible
import HopfieldNet.mathematics.LinearAlgebra.Matrix.Spectrum
import HopfieldNet.Mathematics.Topology.Compactness.ExtremeValueUSC

import HopfieldNet.Papers.Hopfield82.PhaseSpaceFlow
import HopfieldNet.Papers.Hopfield82.MemoryConfusion
import HopfieldNet.Papers.Hopfield82.MemoryStorage
import HopfieldNet.Papers.Hopfield82.EnergyConvergence
import HopfieldNet.SpinState.Basic
import HopfieldNet.SpinState.StochasticUpdate

import HopfieldNet.BM.Core
import HopfieldNet.BM.CoreQuiv
import HopfieldNet.BM.Markov

/-
import HopfieldNet.Tools.ComputableReal.aux_lemmas
import HopfieldNet.Tools.ComputableReal.ComputableReal
import HopfieldNet.Tools.ComputableReal.ComputableRSeq
import HopfieldNet.Tools.ComputableReal.examples
import HopfieldNet.Tools.ComputableReal.IsComputable
import HopfieldNet.Tools.ComputableReal.IsComputableC
import HopfieldNet.Tools.ComputableReal.SpecialFunctions.Basic
import HopfieldNet.Tools.ComputableReal.SpecialFunctions.Exp
import HopfieldNet.Tools.ComputableReal.SpecialFunctions.Pi
import HopfieldNet.Tools.ComputableReal.SpecialFunctions.Sqrt-/
