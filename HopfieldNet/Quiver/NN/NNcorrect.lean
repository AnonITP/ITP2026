/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic

open Mathlib Finset

/--
A `NeuralNetwork` models a neural network with:

- `R`: Type for weights and activations.
- `U`: Type for nodes.
- `[Zero R]`: `R` has a zero element.

It extends `Digraph U` and includes the network's architecture, activation functions, and constraints.
-/
structure NeuralNetwork (R U : Type) [Zero R] extends Digraph U where
  /-- Input nodes. -/
  (Ui Uo Uh : Set U)
  /-- All nodes are either input, output, or hidden. -/
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  /-- There is at least one input node. -/
  (hUi : Ui ≠ ∅)
  /-- There is at least one output node. -/
  (hUo : Uo ≠ ∅)
  /-- Hidden nodes are not input or output nodes. -/
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  /-- Dimensions of input vectors for each node. -/
  (κ1 κ2 : U → ℕ)
  /-- Computes the net input to a node. -/
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
  /-- Computes the activation of a node. -/
  (fact : ∀ u : U, R → Vector R (κ2 u) → R)
  /-- Computes the final output of a node. -/
  (fout : ∀ _ : U, R → R)
  /-- Predicate on activations. -/
  (pact : R → Prop)
  /-- Predicate on weight matrices. -/
  (pw : Matrix U U R → Prop)
  /-- If all activations satisfy `pact`, then the activations computed by `fact` also satisfy `pact`. -/
  (hpact : ∀ (w : Matrix U U R) (_ : ∀ u v, ¬ Adj u v → w u v = 0) (_ : pw w)
   (σ : (u : U) → Vector R (κ1 u)) (θ : (u : U) → Vector R (κ2 u)) (act : U → R),
  (∀ u : U, pact (act u)) → (∀ u : U, pact (fact u (fnet u (w u)
    (fun v => fout v (act v)) (σ u)) (θ u))))

variable {R U : Type} [Zero R]

/-- `Params` is a structure that holds the parameters for a neural network `NN`. -/
structure Params (NN : NeuralNetwork R U) where
  /-- The weight matrix of the neural network. -/
  (w : Matrix U U R)
  /-- A proof that if two nodes are not connected, then the weight is zero. -/
  (hw : ∀ u v, ¬ NN.Adj u v → w u v = 0)
  /-- A proof that the weight matrix satisfies a certain property. -/
  (hw' : NN.pw w)
  /-- A function that assigns a vector to each node. -/
  (σ : ∀ u : U, Vector R (NN.κ1 u))
  /-- A function that assigns another vector to each node. -/
  (θ : ∀ u : U, Vector R (NN.κ2 u))

namespace NeuralNetwork

/--
`Pattern` represents a pattern in a neural network.
-/
structure Pattern (NN : NeuralNetwork R U) where
  /-- A function mapping each node to its activation value. -/
  act : U → R
  /-- A proof that the activations satisfy the required properties. -/
  hp : ∀ u : U, NN.pact (act u)

namespace Pattern

variable {NN : NeuralNetwork R U} (wσθ : Params NN) (s : NN.Pattern)

/-- The output function of a node in the neural network. -/
def out (u : U) : R := NN.fout u (s.act u)

/-- The net function of a node in the neural network. -/
def net (u : U) : R := NN.fnet u (wσθ.w u) (fun v => s.out v) (wσθ.σ u)

/--
`onlyUi` states that if a node `u` is not an input node, then its activation is zero.
-/
def onlyUi : Prop := ∀ u : U, ¬ u ∈ NN.Ui → s.act u = 0

variable [DecidableEq U]

/--
`Up` updates the activation of node `u` in the pattern.
If `v` is `u`, it computes the new activation of `u`.
Otherwise, it keeps the existing activation.
-/
def Up (u : U) : NeuralNetwork.Pattern NN :=
  { act := fun v => if v = u then NN.fact u (s.net wσθ u) (wσθ.θ u) else s.act v, hp := by
      intro v
      split
      · apply NN.hpact
        intros u' v' hu'v'
        exact wσθ.hw u' v' hu'v'
        exact wσθ.hw'
        exact fun u ↦ s.hp u
      · apply s.hp}

/-- `workPhase` updates the initial pattern `extu` for each node in `uOrder` using `s.Up wσθ u`.
It starts with `extu` and returns the final pattern after processing all nodes in `uOrder`. -/
def workPhase (extu : NN.Pattern) (_ : extu.onlyUi) (uOrder : List U) : NN.Pattern :=
  uOrder.foldl (fun s u => s.Up wσθ u) extu

/-- `seqStates` generates a sequence of patterns for the neural network.
- For `n = 0`, it returns the initial pattern `s`.
- For `n > 0`, it updates the pattern at `n - 1` using the node from `useq` at `n - 1`. -/
def seqStates (useq : ℕ → U) : ℕ → NeuralNetwork.Pattern NN
  | 0 => s
  | n + 1 => .Up wσθ (seqStates useq n) (useq n)

/-- `isStable` checks if the state `s` remains unchanged after applying `s.Up wσθ` to every node `u`. -/
def isStable : Prop :=  ∀ (u : U), (s.Up wσθ u).act u = s.act u

end Pattern

end NeuralNetwork

/-- Two nodes `u` and `v` are connected in the graph if `w u v` is not zero. -/
def Matrix.Adj (w : Matrix U U R) : U → U → Prop := fun u v => w u v ≠ 0

/-- `Matrix.w` returns the value of the matrix `w` at position `(u, v)` if `u` and `v` are connected. -/
def Matrix.w (w : Matrix U U R) : ∀ u v : U, w.Adj u v → R := fun u v _ => w u v
