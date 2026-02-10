/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import HopfieldNet.Quiver.NN.NNcorrect

set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset

open Mathlib Finset BigOperators

/-- A 3x3 matrix of rational numbers. --/
def test.M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]

def test : NeuralNetwork ℚ (Fin 3) where
  Adj := test.M.Adj
  Ui := {0,1}
  Uo := {2}
  hU := by
     ext x
     simp only [Set.mem_univ, Fin.isValue, Set.union_singleton,
       Set.union_empty, Set.mem_insert_iff,
       Set.mem_singleton_iff, true_iff]
     revert x
     decide
  Uh := ∅
  hUi := Ne.symm (Set.ne_insert_of_notMem {1} fun a ↦ a)
  hUo := Set.singleton_ne_empty 2
  hhio := by
    simp only [Fin.isValue, Set.union_singleton, Set.empty_inter]
  pw W := True
  κ1 u := 0
  κ2 u := 1
  fnet u w pred σ := ∑ v, w v * pred v
  fact u input θ := if input ≥ θ.get 0 then 1 else 0
  fout u act := act
  pact u := True
  hpact w _ _ σ θ _ pact u := pact u

def wθ : Params test where
  w := test.M
  θ u := ⟨#[1], by
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    unfold test
    simp only⟩
  σ _ := Vector.emptyWithCapacity 0
  hw u v hv := by by_contra h; exact hv h
  hw' := by simp only [test]

instance : Repr (NeuralNetwork.Pattern test) where
  reprPrec state _ :=
   ("acts: " ++ repr (state.act)) ++ ", outs: " ++
        repr (state.out) ++ ", nets: " ++ repr (state.net wθ)

/--
`test.extu` is the initial state for the `test` neural network with activations `[1, 0, 0]`.
-/
def test.extu : test.Pattern := {act := ![1,0,0], hp := fun u => trivial}

lemma zero_if_not_mem_Ui : ∀ u : Fin 3,
  ¬ u ∈ ({0,1} : Finset (Fin 3)) → test.extu.act u = 0 := by decide

/--
If `u` is not in the input neurons `Ui`, then `test.extu.act u` is zero.
-/
lemma test.onlyUi : test.extu.onlyUi := by {
  intros u hu
  apply zero_if_not_mem_Ui u
  simp only [Fin.isValue, mem_insert, mem_singleton, not_or]
  exact not_or.mp hu}

-- Show the state after *each* asynchronous neuron update (not only the final state).

def test.seq : List (Fin 3) := [2,0,1,2,0,1,2]

/-- States after running `workPhase` on every prefix of `test.seq`.
Includes the initial state as the first element (empty prefix). -/
def test.workPhaseTrace : List test.Pattern :=
  (test.seq.inits).map (fun pref =>
    NeuralNetwork.Pattern.workPhase wθ test.extu test.onlyUi pref
  )

-- All intermediate states (including the initial one at the start)
#eval test.workPhaseTrace

/-- Same trace, but labeled by the neuron updated at each step. -/
def test.workPhaseTraceLabeled : List ((Fin 3) × test.Pattern) :=
  List.zip test.seq (test.workPhaseTrace.drop 1)

-- Each step: (neuron updated, resulting state)
#eval test.workPhaseTraceLabeled

-- The workphase for the asynchronous update of the sequence of neurons u3 , u2 , u1 , u3 , u2 , u1 , u3 ,

def test.seq' : List (Fin 3) := [2,1,0,2,1,0,2]

/-- States after running `workPhase` on every prefix of `test.seq'`.
Includes the initial state as the first element (empty prefix). -/
def test.workPhaseTrace' : List test.Pattern :=
  (test.seq'.inits).map (fun pref =>
    NeuralNetwork.Pattern.workPhase wθ test.extu test.onlyUi pref
  )

#eval test.workPhaseTrace'

/-- Same trace, but labeled by the neuron updated at each step. -/
def test.workPhaseTraceLabeled' : List ((Fin 3) × test.Pattern) :=
  List.zip test.seq' (test.workPhaseTrace'.drop 1)

#eval test.workPhaseTraceLabeled'

-- Final state (same as last element of the trace)
#eval NeuralNetwork.Pattern.workPhase wθ test.extu test.onlyUi test.seq'

#exit
/-Hopfield Networks-/

/-- A 4x4 matrix of rational numbers. --/
def W1 : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of ![![0,1,-1,-1], ![1,0,-1,-1], ![-1,-1,0,1], ![-1,-1,1,0]]

/--
`HebbianParamsTest` defines a Hopfield Network with 4 neurons and rational weights.
- `w`: The weight matrix `W1`.
- `hw`: Proof that the weights are symmetric.
- `hw'`: Proof that the weights are zero on the diagonal.
- `σ`: Always an empty vector.
- `θ`: Always returns a list with a single 0.

`extu` is the initial state of this network.
- `act`: Starts as `[1, -1, -1, 1]`.
- `hp`: Proof that the activations are valid.
--/
def HebbianParamsTest : Params (HopfieldNetwork ℚ (Fin 4)) where
  w := W1
  hw u v huv := by
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    revert v v
    simp only [forall_eq']
    revert u u
    decide
  hw' := by {
    unfold HopfieldNetwork
    simp only
    decide}
  σ := fun u => Vector.mkEmpty 0
  θ u := ⟨#[0],by
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]⟩

/--
`extu` is the initial state for our `HebbianParamsTest` Hopfield network.
- `act`: `[1, -1, -1, 1]` - initial activations.
- `hp`: Proof that the activations are valid.

This initializes the state for a Hopfield network test.
--/
def extu : State HebbianParamsTest where
  act := ![1,-1,-1,1]
  hp := by
    intros u
    unfold HopfieldNetwork
    simp only
    revert u
    decide

instance : Repr (HopfieldNetwork ℚ (Fin 4)).Pattern where
  reprPrec state _ := ("acts: " ++ repr (state.act))

-- Computations

-- lemma zero_if_not_mem_Ui' : ∀ u : Fin 4,
--     ¬ u ∈ ({0,1,2,3} : Finset (Fin 4)) → extu.act u = 0 := by {decide}

-- def HN.hext : extu.onlyUi := by {intros u; tauto}

-- #eval NeuralNetwork.Pattern.workPhase HebbianParamsTest extu HN.hext [2,0,1,2,0,1,2]


/--
`pattern_ofVec` converts a pattern vector from `Fin n` to `ℚ` into a `Pattern`
for a `HopfieldNetwork` with `n` neurons.
It checks if all elements are either 1 or -1. If they are, it returns `some`
 pattern; otherwise, it returns `none`.
--/
def pattern_ofVec {n} [NeZero n] (pattern : Fin n → ℚ) :
    Option (HopfieldNetwork ℚ (Fin n)).Pattern :=
  if hp : ∀ i, pattern i = 1 ∨ pattern i = -1 then
    some {act := pattern, hp := by {
      intros u
      unfold HopfieldNetwork
      simp only
      apply hp
      }}
  else
    none

/--
`obviousFunction` tries to convert a function `f` from `α` to `Option β` into a regular function
from `α` to `β`. If `f` returns `some` for every input, it returns `some` function that extracts
these values. Otherwise, it returns `none`.
--/
def obviousFunction [Fintype α] (f : α → Option β) : Option (α → β) :=
  if h : ∀ x, (f x).isSome then
    some (fun a => (f a).get (h a))
  else
    none

/--
`patternToNet` converts a matrix `V` (a function from `Fin m` to `Fin n` to `ℚ`)
into a function that maps each row to a `Pattern` for a `HopfieldNetwork` with `Fin n` neurons.
It checks if all elements of each row are either 1 or -1. If they are, it returns
`some` function that maps each row to a `Pattern`; otherwise, it returns `none`.

Parameters:
- `V`: A matrix represented as a function from `Fin m` to `Fin n` to `ℚ`.
- `[NeZero n]`: Ensures that `n` is non-zero.
- `hmn`: Proof that `m` is less than `n`.

Returns:
- An `Option` containing a function from `Fin m` to
`HopfieldNetwork ℚ (Fin n)).Pattern`, or `none` if the conversion is not possible.
--/
def patternToNet (V : Fin m → Fin n → ℚ) [NeZero n] (hmn : m < n) :
  Option (Fin m → (HopfieldNetwork ℚ (Fin n)).Pattern) :=
  obviousFunction (fun i => pattern_ofVec (V i))

/--
`ZeroParams_4` defines a simple Hopfield Network with 4 neurons.

- `w`: A 4x4 weight matrix filled with zeros.
- `hw`: Proof that the weight matrix is symmetric.
- `hw'`: Proof that the weight matrix has zeros on the diagonal.
- `σ`: An empty vector for each neuron.
- `θ`: A threshold of 0 for each neuron, with proof that the list has length 1.
--/
def ZeroParams_4 : Params (HopfieldNetwork ℚ (Fin 4)) where
  w :=  (Matrix.of ![![0,0,0,0], ![0,0,0,0], ![0,0,0,0], ![0,0,0,0]])
  hw u v huv := by {
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    revert v v
    simp only [forall_eq']
    revert u u
    decide}
  hw' := by {
    unfold HopfieldNetwork
    simp only
    decide}
  σ u := Vector.mkEmpty 0
  θ u := ⟨#[0], by {simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]}⟩

/--
`ps` are two patterns represented by a 2x4 matrix of rational numbers.
--/
def ps : Fin 2 → Fin 4 → ℚ := ![![1,1,-1,-1], ![-1,1,-1,1]]

/--
`test_params` sets up a `HopfieldNetwork` with 4 neurons.
It converts the patterns `ps` into a network using Hebbian learning if possible.
If not, it defaults to `ZeroParams_4`.
--/
def test_params : Params (HopfieldNetwork ℚ (Fin 4)) :=
  match (patternToNet ps (by simp only [Nat.succ_eq_add_one, zero_add,
    Nat.reduceAdd, Nat.reduceLT])) with
  | some patterns => Hebbian patterns
  | none => ZeroParams_4

/--
`useq_Fin n` maps a natural number `i` to an element of `Fin n` (a type with `n` elements).
It wraps `i` around using modulo `n`.

Arguments:
- `n`: The size of the finite type (must be non-zero).
- `i`: The natural number to convert.

Returns:
- An element of `Fin n`.
--/
def useq_Fin n [NeZero n] : ℕ → Fin n := fun i =>
  ⟨_, Nat.mod_lt i (Nat.pos_of_neZero n)⟩

lemma useq_Fin_cyclic n [NeZero n] : cyclic (useq_Fin n) := by
  unfold cyclic
  unfold useq_Fin
  simp only [Fintype.card_fin]
  apply And.intro
  · intros u
    use u.val
    cases' u with u hu
    simp only
    simp_all only [Fin.mk.injEq]
    exact Nat.mod_eq_of_lt hu
  · intros i j hij
    exact Fin.mk.inj_iff.mpr hij

lemma useq_Fin_fair n [NeZero n] : fair (useq_Fin n) :=
  cycl_Fair (useq_Fin n) (useq_Fin_cyclic n)

#eval HopfieldNet_stabilize test_params extu (useq_Fin 4) (useq_Fin_fair 4)

#eval HopfieldNet_conv_time_steps test_params extu (useq_Fin 4) (useq_Fin_cyclic 4)
