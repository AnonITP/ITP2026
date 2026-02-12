import Mathlib.Analysis.SpecialFunctions.Exp
import HopfieldNet.Quiver.NN.Main

namespace Sequential

-- class HasActivations (R : Type) where
--   relu : R → R
--   sigmoid : R → R
--   tanh : R → R

-- inductive Activation
--   | Linear
--   | ReLU
--   | Sigmoid
--   | Tanh
--   deriving DecidableEq, Repr

-- noncomputable instance : HasActivations Real where
--   relu x := max 0 x
--   sigmoid x := 1 / (1 + Real.exp (-x))
--   tanh x := Real.tanh x

/--
A `SequentialArch ζ` specifies the *architecture* of a sequential (feed-forward) neural network
purely at the level of metadata: a list of layer widths together with a corresponding list of
activation descriptors.

Fields:
* `layerWidths : List ℕ` — widths of successive layers; e.g. `[4, 16, 3]` means
  4 input neurons, 16 hidden neurons, and 3 output neurons.
* `activations : List ζ` — activation identifiers/descriptions, one for each layer.

Invariants:
* `h_len_eq` enforces that `layerWidths` and `activations` have the same length.
* `h_min_layers` enforces that there are at least two layers (input and output).
* `h_pos_widths` enforces that every width appearing in `layerWidths` is strictly positive.
-/
structure SequentialArch (ζ : Type) where
  layerWidths : List ℕ
  activations  : List ζ
  h_len_eq     : layerWidths.length = activations.length
  h_min_layers : layerWidths.length ≥ 2
  h_pos_widths : ∀ w ∈ layerWidths, w > 0


-- /-- The Generic Interpreter.-/
-- def apply_act {R : Type} [HasActivations R] (a : Activation) (x : R) : R :=
--   match a with
--   | .Linear  => x  -- Identity works for everything
--   | .ReLU    => HasActivations.relu x
--   | .Sigmoid => HasActivations.sigmoid x
--   | .Tanh    => HasActivations.tanh x

variable (R : Type) [Semiring R]

/--
  We identify a neuron in the graph by a pair: (Layer Index, Neuron Index).
  This maps the sequential structure to a set of vertices U.
-/
structure SeqNeuron (arch : SequentialArch ζ) where
  layerIdx : Fin arch.layerWidths.length
  neuronIdx : Fin (arch.layerWidths.get layerIdx)

instance (arch : SequentialArch ζ) : DecidableEq (SeqNeuron arch) :=
  fun a b => match a, b with
  | ⟨l1, n1⟩, ⟨l2, n2⟩ =>
    if h : l1 = l2 then
      if h2 : n1.val = n2.val then isTrue (by aesop)
      else isFalse (by intro eq; injection eq; aesop)
    else isFalse (by intro eq; injection eq; contradiction)

/--
  Adjacency definition for a Sequential Network (incoming edges):
  `Adj u v` means that `v` is in the immediate previous layer of `u`.
  This matches the forward-pass computation which sums over neurons `v` in the previous layer.
-/
def SeqAdj {arch : SequentialArch ζ} (u v : SeqNeuron arch) : Prop :=
  v.layerIdx.val + 1 = u.layerIdx.val

/--
  Converting the Sequential Architecture into a NeuralNetwork.
-/
def toNeuralNetwork (arch : SequentialArch ζ) (act_map : ζ → R → R) :
    NeuralNetwork R (SeqNeuron arch) R := {
  Hom u v := PLift (SeqAdj u v)
  Ui := { u | u.layerIdx.val = 0 }
  Uo := { u | u.layerIdx.val = arch.layerWidths.length - 1 }
  Uh := { u | u.layerIdx.val > 0 ∧ u.layerIdx.val < arch.layerWidths.length - 1 }
  hUi := by
    have hlen : 0 < arch.layerWidths.length := by
      have := arch.h_min_layers
      omega
    let layer0 : Fin arch.layerWidths.length := ⟨0, hlen⟩
    have h0width : 0 < arch.layerWidths.get layer0 := by
      have hw : arch.layerWidths.get layer0 > 0 :=
        arch.h_pos_widths (arch.layerWidths.get layer0) (by simp)
      simpa using hw
    let neuron0 : Fin (arch.layerWidths.get layer0) := ⟨0, h0width⟩
    refine Set.nonempty_iff_ne_empty'.mp ?_
    exact ⟨⟨layer0, neuron0⟩, rfl⟩
  hUo := by
    refine Set.nonempty_iff_ne_empty'.mp ?_
    have hlast : arch.layerWidths.length - 1 < arch.layerWidths.length := by
      cases h : arch.layerWidths.length with
      | zero =>
          have : ¬ (0 ≥ 2) := by decide
          exact (this (by simpa [h] using arch.h_min_layers)).elim
      | succ n => simp
    let last_Id : Fin arch.layerWidths.length := ⟨arch.layerWidths.length - 1, hlast⟩
    have h0width : 0 < arch.layerWidths.get last_Id := by
      have hw : arch.layerWidths.get last_Id > 0 :=
        arch.h_pos_widths (arch.layerWidths.get last_Id) (by simp)
      simpa using hw
    let neuron0 : Fin (arch.layerWidths.get last_Id) := ⟨0, h0width⟩
    exact ⟨⟨last_Id, neuron0⟩, rfl⟩
  hU := by ext x; simp; omega
  hhio := by ext x; simp; omega
  -- κ1 := fun u => if h : u.layerId.val = 0 then 0
  --   else (arch.layerWidths.get ⟨u.layerId.val - 1, by omega⟩)
  κ1 := fun u => if u.layerIdx.val = 0 then 0 else 1
  κ2 := fun _ => 0
  fnet := fun u w_row act_map params =>
    if h : u.layerIdx.val = 0 then 0
    else
      -- 1. Identify prev layer
      let prev_Id : Fin arch.layerWidths.length := ⟨u.layerIdx.val - 1, by omega⟩
      let prev_width := arch.layerWidths.get prev_Id

      -- 2. Weighted Sum
      let dot_prod := Finset.sum (Finset.univ : Finset (Fin prev_width)) (fun i =>
        let v : SeqNeuron arch := ⟨prev_Id, i⟩
        (w_row v) * (act_map v)
      )
      -- We use `simp [h]` to prove that since layer != 0, the param vector size is 1.
      dot_prod + (params.get ⟨0, by simp [h];⟩)
  fout := fun _ x => x
  fact := fun u x _ _ =>
    if u.layerIdx.val = 0 then
      x
    else
      let act_Id : Fin arch.activations.length := u.layerIdx.cast arch.h_len_eq
      let act_label := arch.activations.get act_Id
      act_map act_label x
  pact := fun _ => True
  pw := fun _ _ _ => True
  hpact := fun _ _ _ _ _ _ _ _ _ => trivial
  pm _ := True
  m := fun _ => 0
}

variable {R : Type} [Semiring R] [DecidableEq R] (ζ : Type) (act_map : ζ → R → R)

open NeuralNetwork

/-- The specific Neural Network instance derived from a Sequential Architecture. -/
abbrev SeqNet (arch : SequentialArch ζ) : NeuralNetwork R (SeqNeuron arch) R :=
  toNeuralNetwork (R := R) arch act_map

/-- A State for a sequential network is just a mapping from (Layer, Index) to a value. -/
abbrev SeqState (arch : SequentialArch ζ)  := NeuralNetwork.State (SeqNet (R:=R) ζ act_map arch)

/-- Parameters for a sequential network. -/
abbrev SeqParams (arch : SequentialArch ζ):= Params (SeqNet (R:=R) ζ act_map arch)

/--
  A generic NeuralNetwork allows updating neurons in *any* order.
  A Sequential Network implies a specific order: Layer 1, then Layer 2, etc.

  We define a function that generates this specific list of neurons.
-/
def sequentialOrder (arch : SequentialArch ζ) : List (SeqNeuron arch) :=
  -- We iterate from layer 1 (first hidden) to the last layer.
  -- Layer 0 (Input) is usually fixed by the external input and not "updated" by the network function.
  let updateLayers : List (Fin arch.layerWidths.length) :=
    (List.finRange arch.layerWidths.length).drop 1 -- Skip layer 0

  updateLayers.flatMap (fun layerId => by
    let w := arch.layerWidths.get layerId
    let neurons : List (Fin w) := List.finRange w
    apply neurons.map
    intros neuronId
    exact { layerIdx := layerId, neuronIdx := neuronId }
  )

/-- Generates list of neurons: Layer 1, then Layer 2, etc. -/
def sequentialOrder' (arch : SequentialArch ζ) : List (SeqNeuron arch) :=
  let layers := (List.finRange arch.layerWidths.length).drop 1
  layers.flatMap (fun l =>
    (List.finRange (arch.layerWidths.get l)).map (fun n => ⟨l, n⟩)
  )

variable (arch : SequentialArch ζ) (params : SeqParams (R:=R) ζ act_map arch)
         (inputState : SeqState (R:=R) ζ act_map arch)

/-- This is the forward pass. We take an initial state (with inputs set) and run
  the updates in the specific `sequentialOrder`.
-/
def forwardPass (inputState : SeqState (R:=R) ζ act_map arch) (h_init : inputState.onlyUi) :
  SeqState (R := R ) ζ act_map arch :=
  -- We use the general `workPhase` but force the order to be `sequentialOrder`
  State.workPhase params inputState h_init (sequentialOrder ζ arch)

-- Helper 1: Topological property
omit [DecidableEq R] in
lemma pred_layer_lt (arch : SequentialArch ζ) {u v : SeqNeuron arch}
    (h : (SeqNet (R := R) ζ act_map arch).Hom u v) : v.layerIdx < u.layerIdx := by
  unfold SeqNet toNeuralNetwork at h
  have hv : v.layerIdx.val + 1 = u.layerIdx.val := by
    simpa [SeqAdj] using h.down
  exact Fin.lt_def.2 (by omega)

-- Helper 2: Input neurons are stable
omit [DecidableEq R] in
lemma input_is_stable (arch : SequentialArch ζ)
  (params : SeqParams (R := R) ζ act_map arch) (s : SeqState (R := R) ζ act_map arch)
  (u : SeqNeuron arch) (hu : u.layerIdx.val = 0) :
  (s.Up params u).act u = s.act u := by
  simp [State.Up, toNeuralNetwork, hu]

-- 1. The User defines their specific needs
inductive CustomActivations
  | MyReLU
  | MySoftplus -- Something your library didn't have!
  | MyIdentity

-- 2. The User defines the interpreter for their type R
def my_interpreter (R : Type) [LinearOrder R] [Zero R] :
    CustomActivations → R → R
  | .MyReLU, x => max 0 x
  | .MySoftplus, x => x -- (Assume logic here)
  | .MyIdentity, x => x

-- 3. The User defines the Architecture
def exArch : SequentialArch CustomActivations := {
  layerWidths := [2, 2, 1]
  activations  := [.MyIdentity, .MyReLU, .MySoftplus]
  h_len_eq     := rfl
  h_min_layers := by decide
  h_pos_widths := by decide
}
-- Define the Weights and Biases
-- Input: [x, y]
-- Hidden 1: ReLU(1*x - 1*y)  (Difference)
-- Hidden 2: ReLU(1*y - 1*x)  (Inverse Difference)
-- Output:   H1 + H2          (Absolute Difference |x-y|)

def exParams : SeqParams (R := ℚ) (ζ := CustomActivations) (act_map := my_interpreter ℚ) exArch := {
  -- A. Biases (stored in ζ)
  -- Input neurons (layer 0) have size 0. Others have size 1.
  σ := fun u => by
    by_cases h : u.layerIdx.val = 0
    · -- input layer: κ1 u = 0
      simpa [SeqNet, toNeuralNetwork, h] using (Vector.replicate 0 (0 : ℚ))
    · -- hidden/output layers: κ1 u = 1
      simpa [SeqNet, toNeuralNetwork, h] using (Vector.replicate 1 (0 : ℚ))
      -- Bias is 0 for all hidden/output nodes

  -- B. Activation Params (stored in θ)
  -- Unused for ReLU, always size 0
  θ := fun _ => Vector.replicate 0 (0 : ℚ)

  -- C. Weights (Matrix)
  -- We define connections based on layer/neuron indices.
  -- Also, we force weights to be 0 whenever there is no edge (`¬Adj u v`),
  -- so the `hw` obligation is solved by simp.
  w := fun u v =>
    if hv : v.layerIdx.val + 1 = u.layerIdx.val then
      match u.layerIdx.val, u.neuronIdx.val, v.layerIdx.val, v.neuronIdx.val with
      -- Connection: Layer 0 -> Layer 1
      | 1, 0, 0, 0 =>  1  -- x -> H1
      | 1, 0, 0, 1 => -1  -- y -> H1
      | 1, 1, 0, 0 => -1  -- x -> H2
      | 1, 1, 0, 1 =>  1  -- y -> H2

      -- Connection: Layer 1 -> Layer 2 (Output)
      | 2, 0, 1, 0 => 1   -- H1 -> Out
      | 2, 0, 1, 1 => 1   -- H2 -> Out

      -- No other connections
      | _, _, _, _ => 0
    else
      0

  -- D. Proofs
  hw := by
    intro u v h1
    have h' : ¬ (v.layerIdx.val + 1 = u.layerIdx.val) := by
      intro hv
      apply h1
      simpa [SeqNet, toNeuralNetwork, SeqAdj] using (hv)
    simp [h']
  hw' := trivial
  h_arrows := by
    intro u v
    simp [toNeuralNetwork, SeqAdj]
}

-- 4. Define Initial State (Input)
-- Let's test inputs x=10, y=15.
-- Expected Result: |10 - 15| = 5.
def exInputState :
    SeqState (R := ℚ) (ζ := CustomActivations) (act_map := my_interpreter ℚ) exArch := {
  act := fun u =>
    match u.layerIdx.val, u.neuronIdx.val with
    | 0, 0 => 10 -- Input x
    | 0, 1 => 15 -- Input y
    | _, _ => 0  -- Initialize others to 0
  hp := fun _ => trivial
}

-- Proof that only inputs are set
lemma exOnlyUi : exInputState.onlyUi := by
  constructor
  intro u hu
  -- If u is not in Layer 0, exInputState returns 0.
  simp [toNeuralNetwork] at hu
  cases u with
  | mk l n =>
    have hl : l.val ≠ 0 := by
      simpa using hu
    cases h : l.val with
    | zero =>
        exfalso
        exact hl (by simpa using h)
    | succ k =>

        -- Since layerId ≠ 0, the match falls through to the default case.
        simp [exInputState, h]
        aesop

-- This prints the state layer-by-layer
def showState
    (s : SeqState (R := ℚ) (ζ := CustomActivations) (act_map := my_interpreter ℚ) exArch) :
    String :=
  let layers := List.finRange exArch.layerWidths.length
  String.intercalate "\n" (layers.map (fun l =>
    let width := exArch.layerWidths.get l
    let neurons := List.finRange width
    let acts := neurons.map (fun n => toString (s.act ⟨l, n⟩))
    s!"Layer {l}: {acts}"
  ))

def finalState :
    SeqState (R := ℚ) (ζ := CustomActivations) (act_map := my_interpreter ℚ) exArch :=
  forwardPass (R := ℚ) (ζ := CustomActivations) (act_map := my_interpreter ℚ)
    exArch exParams exInputState exOnlyUi

#eval showState finalState

end Sequential
