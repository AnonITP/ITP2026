import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.List.Pairwise

open Mathlib

universe u v

structure NeuralNetwork (R U : Type u) [Zero R] extends Quiver.{v,u} U where
  (Ui Uo Uh : Set U)
  (hUi : Ui ≠ ∅)
  (hUo : Uo ≠ ∅)
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  (κ1 κ2 : U → ℕ)
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
    /-- Computes the activation of a node. -/
  (fact : ∀ u : U, R → Vector R (κ2 u) → R)
  (fout : ∀ _ : U, R → R)
  (pact : R → Prop)
  (pw : ∀ (u v : U), (u ⟶ v) → Prop)
  -- /-- The adjacency matrix induced by `pw`: entry `(u,v)` holds iff there exists an arrow `u ⟶ v`
  -- satisfying `pw`. -/
  (pwMat : Matrix U U Prop := fun u v => ∃ f : (u ⟶ v), pw u v f)
  /-- NEW: Predicate on Matrix: Defines valid weights (e.g., "weights must be between -1 and 1"). -/
  (pm : Matrix U U R → Prop)
    /-- If all activations satisfy `pact`, then the activations computed by `fact` also satisfy `pact`. -/
  (hpact : ∀ (w : Matrix U U R) (_ : ∀ (u v : U), ¬pwMat u v → w u v = 0)
   (_ : ∀ u v (f : Hom u v), pw u v f)
   (_ : pm w)
   (σ : (u : U) → Vector R (κ1 u))
   (θ : (u : U) → Vector R (κ2 u))
   (act : U → R),
  (∀ u : U, pact (act u)) → (∀ u : U, pact (fact u (fnet u (w u)
    (fun v => fout v (act v)) (σ u)) (θ u))))

variable {R U : Type} [Zero R]

/--
`Params` is a structure that holds the external parameters for a given
neural network `NN`, along with a proof that the network's internal
parameters (its arrows) satisfy the required predicate `NN.pw`.
-/
structure Params (NN : NeuralNetwork R U) where
  /-- A proof that all arrows in the neural network satisfy its parameter predicate `pw`. -/
  (h_arrows : ∀ u v (f : NN.Hom u v), NN.pw u v f)
  (w : Matrix U U R)
  /-- External parameters for the `fnet` function (e.g., biases). -/
  (σ : ∀ u : U, Vector R (NN.κ1 u))
  /-- External parameters for the `fact` function (e.g., activation function parameters). -/
  (θ : ∀ u : U, Vector R (NN.κ2 u))
  /-- The equivalent of `hw`: If there is no valid arrow between u and v, the weight must be 0. -/
  (hw : ∀ u v, ¬ NN.pwMat u v → w u v = 0)
  -- /-- 4. Matrix Validity (hw'):
  --     The matrix `w` must satisfy the global parameter predicate `pm`. -/
  (hw' : NN.pm w)

namespace NeuralNetwork

structure State (NN : NeuralNetwork R U) where
  act : U → R
  hp : ∀ u : U, NN.pact (act u)

/-- Extensionality lemma for neural network states -/
@[ext]
lemma ext {R U : Type} [Zero R] {NN : NeuralNetwork R U}
    {s₁ s₂ : NN.State} : (∀ u, s₁.act u = s₂.act u) → s₁ = s₂ := by
  intro h
  cases s₁
  cases s₂
  simp only [NeuralNetwork.State.mk.injEq]
  apply funext
  exact h

namespace State

variable {NN : NeuralNetwork R U} (wσθ : Params NN) (s : NN.State)

def out (u : U) : R := NN.fout u (s.act u)
def net (u : U) : R := NN.fnet u (wσθ.w u) (fun v => s.out v) (wσθ.σ u)
def onlyUi : Prop := ∀ u : U, ¬ u ∈ NN.Ui → s.act u = 0

variable [DecidableEq U]

def Up (u : U) : NeuralNetwork.State NN :=
  { act := fun v => if v = u then NN.fact u (s.net wσθ u) (wσθ.θ u) else s.act v, hp := by
      intro v
      split
      · apply NN.hpact
        intros u' v' hu'v'
        exact wσθ.hw u' v' hu'v'
        exact wσθ.h_arrows
        exact wσθ.hw'
        exact fun u ↦ s.hp u
      · apply s.hp}

def workPhase (extu : NN.State) (_ : extu.onlyUi) (uOrder : List U) : NN.State :=
  uOrder.foldl (fun s_iter u_iter => s_iter.Up wσθ u_iter) extu

/-- `seqStates` generates a sequence of patterns for the neural network.
- For `n = 0`, it returns the initial pattern `s`.
- For `n > 0`, it updates the pattern at `n - 1` using the node from `useq` at `n - 1`. -/
def seqStates (useq : ℕ → U) : ℕ → NeuralNetwork.State NN
  | 0 => s
  | n + 1 => .Up wσθ (seqStates useq n) (useq n)

def isStable : Prop :=  ∀ (u : U), (s.Up wσθ u).act u = s.act u

end State
end NeuralNetwork
