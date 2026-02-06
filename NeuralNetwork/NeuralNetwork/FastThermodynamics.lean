import NeuralNetwork.NeuralNetwork.FastBoltzmannEval
import NeuralNetwork.NeuralNetwork.FastMarkovMatrix

/-!
# Executable thermodynamics (FastReal / Ball)

This module provides **computable**, interval-certified enclosures for:

- `log Z` (log partition function),
- free energy in the normalized units \(F = -kBT \log Z\) (user supplies `kBT`), and
- Shannon entropy in units \(k_B = 1\): \(S = -\sum_s p(s)\log p(s)\).

All functions are *partial* (`Option`) because `log` requires certified positivity
and division requires certified separation from `0`.
-/

namespace NeuralNetwork
namespace FastThermodynamics

open Computable.Fast
open NeuralNetwork.FastFiniteEvalExplicit

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U] [FiniteEnum U]

abbrev NNQ : NeuralNetwork ℚ U ℚ := TwoState.SymmetricBinary ℚ U

/-- `log Z` where `Z = ∑ exp(-β E(s))` is computed via `FastBoltzmannEval.partitionFunction`. -/
def logPartition? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball :=
  FastReal.log? (NeuralNetwork.FastBoltzmannEval.partitionFunction (U := U) β p)

/-- Mean energy \(U = \sum_s E(s)\,p(s)\), computed as \((\sum_s E(s)w(s)) / Z\). -/
def meanEnergy? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let E := NeuralNetwork.FastBoltzmannEval.energyFast (U := U) p
  let w : (NNQ (U := U)).State → FastReal := fun s =>
    FastReal.exp (-(β * (E s)))
  let num : FastReal :=
    FastFiniteEvalExplicit.sum (ι := (NNQ (U := U)).State) (fun s => (E s) * (w s))
  let Z : FastReal := NeuralNetwork.FastBoltzmannEval.partitionFunction (U := U) β p
  num.div? Z n

/-- Mean square energy \(E[E^2] = \sum_s E(s)^2\,p(s)\), computed as \((\sum_s E(s)^2 w(s)) / Z\). -/
def meanSquareEnergy? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let E := NeuralNetwork.FastBoltzmannEval.energyFast (U := U) p
  let w : (NNQ (U := U)).State → FastReal := fun s =>
    FastReal.exp (-(β * (E s)))
  let num : FastReal :=
    FastFiniteEvalExplicit.sum (ι := (NNQ (U := U)).State) (fun s => (E s) * (E s) * (w s))
  let Z : FastReal := NeuralNetwork.FastBoltzmannEval.partitionFunction (U := U) β p
  num.div? Z n

/-- Energy variance `Var(E) = E[E^2] - (E[E])^2` (units `kB = 1`). -/
def energyVariance? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let prec : Int := -((n : Int) + 2)
  let u ← meanEnergy? (U := U) β p n
  let u2 ← meanSquareEnergy? (U := U) β p n
  let uSq := Ball.mul u u prec
  pure (Ball.add u2 (Ball.neg uSq) prec)

/-- Heat capacity in `kB = 1` units:

\[
  C = \mathrm{Var}(E) / T^2 = β^2 \,\mathrm{Var}(E)
\]

This is the standard finite canonical identity. -/
def heatCapacityBeta? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let prec : Int := -((n : Int) + 2)
  let var ← energyVariance? (U := U) β p n
  let βb : Ball := β (n + 10)
  let β2 : Ball := Ball.mul βb βb prec
  pure (Ball.mul β2 var prec)

/-- Free energy in "kBT units": \(F = -(kBT)\log Z\). -/
def freeEnergyKBT? (β : FastReal) (p : Params (NNQ (U := U))) (kBT : FastReal) :
    ℕ → Option Ball := fun n => do
  let prec : Int := -((n : Int) + 2)
  let lZ ← logPartition? (U := U) β p n
  pure (Ball.neg (Ball.mul (kBT (n + 10)) lZ prec))

/-- Free energy in "β units": \(F = -\log Z / β\) (i.e. `kB = 1`, `T = 1/β`). -/
def freeEnergyBeta? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let prec : Int := -((n : Int) + 2)
  let lZ ← logPartition? (U := U) β p n
  let invβ ← FastReal.inv? β n
  pure (Ball.neg (Ball.mul lZ invβ prec))

/-- Shannon entropy (in units `kB = 1`): \(S = -\sum_s p(s)\log p(s)\). -/
def shannonEntropy? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let ps ← NeuralNetwork.FastMarkovMatrix.boltzmannVec? (U := U) β p n
  let prec : Int := -((n : Int) + 2)
  let mut acc : Ball := Ball.zero
  for q in ps do
    let lq ← Ball.log? q prec
    acc := Ball.add acc (Ball.mul q lq prec) prec
  pure (Ball.neg acc)

/-- Entropy via the canonical identity \(S = β\,U + \log Z\) (units `kB = 1`).

This avoids `log p(s)` and is therefore much more robust computationally. -/
def entropyViaMeanEnergy? (β : FastReal) (p : Params (NNQ (U := U))) : ℕ → Option Ball := fun n => do
  let prec : Int := -((n : Int) + 2)
  let lZ ← logPartition? (U := U) β p n
  let Umean ← meanEnergy? (U := U) β p n
  let βb : Ball := β (n + 10)
  pure (Ball.add (Ball.mul βb Umean prec) lZ prec)

end FastThermodynamics
end NeuralNetwork
