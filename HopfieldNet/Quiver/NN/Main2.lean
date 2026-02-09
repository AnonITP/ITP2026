import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.List.Pairwise

open Mathlib

universe u v u₁ u₂

structure NeuralNetwork' (R : Type uR) (U : Type uU) (σ : Type uσ) [Zero R] extends Digraph U where
  /-- Input neurons. -/
  (Ui Uo Uh : Set U)
  /-- There is at least one input neuron. -/
  (hUi : Ui ≠ ∅)
  /-- There is at least one output neuron. -/
  (hUo : Uo ≠ ∅)
  /-- All neurons are either input, output, or hidden. -/
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  /-- Hidden neurons are not input or output neurons. -/
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  /-- Dimensions of input vectors for each neuron. -/
  (κ1 κ2 : U → ℕ)
  /-- Computes the net input to a neuron. -/
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
  /-- Computes the activation of a neuron (polymorphic σ). -/
  (fact : ∀ u : U, σ → R → Vector R (κ2 u) → σ) -- current σ, net input, params → σ
  /-- Converts an activation value to a numeric output for computation. -/
  (fout : ∀ _ : U, σ → R)
  /-- Optional helper map σ → R (can be same as fout u if independent of u). -/
  (m : σ → R)
  /-- Predicate on activations (in σ). -/
  (pact : σ → Prop)
  /-- Predicate on weight matrices. -/
  (pw : Matrix U U R → Prop)
  /-- If all activations satisfy `pact`, then the next activations computed by `fact`
  also satisfy `pact`. -/
  (hpact :
    ∀ (w : Matrix U U R)
      (_ : ∀ u v, ¬ Adj u v → w u v = 0) (_ : pw w)
      (σv : (u : U) → Vector R (κ1 u))
      (θ : (u : U) → Vector R (κ2 u))
      (current : U → σ),
      (∀ u_idx : U, pact (current u_idx)) →
      ∀ u_target : U,
        pact (fact u_target (current u_target)
                (fnet u_target (w u_target) (fun v => fout v (current v)) (σv u_target))
                (θ u_target)))

structure NeuralNetwork (R : Type u₁) (U : Type u) (σ : Type u₂) [Zero R] extends Quiver.{v,u} U where
  (Ui Uo Uh : Set U)
  (hUi : Ui ≠ ∅)
  (hUo : Uo ≠ ∅)
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  (κ1 κ2 : U → ℕ)
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
  --(fact : ∀ u : U, R → R → Vector R (κ2 u) → R)
  (fact : ∀ u : U, σ → R → Vector R (κ2 u) → σ)
  (fout : ∀ _ : U, σ → R)

  (pact : σ → Prop)
    /-- Optional helper map σ → R (can be same as fout u if independent of u). -/
  (m : σ → R)

  (pw : ∀ (u v : U), (u ⟶ v) → Prop)
  -- /-- The adjacency matrix induced by `pw`: entry `(u,v)` holds iff there exists an arrow `u ⟶ v`
  -- satisfying `pw`. -/
  (pwMat : Matrix U U Prop := fun u v => ∃ f : (u ⟶ v), pw u v f)
  /-- Predicate on Matrix: Defines valid weights (e.g., "weights must be between -1 and 1"). -/
  (pm : Matrix U U R → Prop)
  (hpact : ∀

  (w : Matrix U U R)
  (_ : ∀ (u v : U), ¬pwMat u v → w u v = 0)
  (_ : ∀ u v (f : Hom u v), pw u v f)
  (_ : pm w)

  (σv : (u : U) → Vector R (κ1 u))
  (θ : (u : U) → Vector R (κ2 u))

  (current_neuron_activations : U → σ),
  (∀ u_idx : U, pact (current_neuron_activations u_idx)) → -- Precondition on all current activations
  (∀ u_target : U, pact (fact u_target (current_neuron_activations u_target) -- Pass current_act of target neuron
                               (fnet u_target (w u_target) (fun v => fout v (current_neuron_activations v)) (σv u_target))
                               (θ u_target))))

variable {R U σ : Type} [Zero R]

/--
`Params` is a structure that holds the external parameters for a given
neural network `NN`, along with a proof that the network's internal
parameters (its arrows) satisfy the required predicate `NN.pw`.
-/
structure Params (NN : NeuralNetwork R U σ) where
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

structure State (NN : NeuralNetwork R U σ) where
  act : U → σ
  hp : ∀ u : U, NN.pact (act u)

/-- Extensionality lemma for neural network states -/
@[ext]
lemma ext {R U σ : Type} [Zero R] {NN : NeuralNetwork R U σ}
    {s₁ s₂ : NN.State} : (∀ u, s₁.act u = s₂.act u) → s₁ = s₂ := by
  intro h
  cases s₁
  cases s₂
  simp only [NeuralNetwork.State.mk.injEq]
  apply funext
  exact h

namespace State

variable {NN : NeuralNetwork R U σ} (wσθ : Params NN) (s : NN.State)

def out (u : U) : R := NN.fout u (s.act u)
def net (u : U) : R := NN.fnet u (wσθ.w u) (fun v => s.out v) (wσθ.σ u)
def onlyUi : Prop := ∃ σ0 : σ, ∀ u : U, ¬ u ∈ NN.Ui → s.act u = σ0

variable [DecidableEq U]

def Up {NN_local : NeuralNetwork R U σ} (s : NN_local.State) (wσθ : Params NN_local) (u_upd : U) :
    NN_local.State :=
  { act := fun v => if v = u_upd then
                      NN_local.fact u_upd (s.act u_upd)
                        (NN_local.fnet u_upd (wσθ.w u_upd) (fun n => s.out n) (wσθ.σ u_upd))
                        (wσθ.θ u_upd)
                    else
                      s.act v,
    hp := by
      intro v_target
      rw [ite_eq_dite]
      split_ifs with h_eq_upd_neuron
      · apply NN_local.hpact
        exact wσθ.hw
        exact wσθ.h_arrows
        exact wσθ.hw'
        · exact s.hp
      · exact s.hp v_target
  }

def workPhase (extu : NN.State) (_ : extu.onlyUi) (uOrder : List U) : NN.State :=
  uOrder.foldl (fun s_iter u_iter => s_iter.Up wσθ u_iter) extu

def seqStates (useq : ℕ → U) : ℕ → NeuralNetwork.State NN
  | 0 => s
  | n + 1 => .Up (seqStates useq n) wσθ (useq n)

def isStable : Prop :=  ∀ (u : U), (s.Up wσθ u).act u = s.act u

end State
end NeuralNetwork
