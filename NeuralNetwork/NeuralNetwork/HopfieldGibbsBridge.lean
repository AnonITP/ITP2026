import NeuralNetwork.NeuralNetwork.HopfieldEnergySpec
import NeuralNetwork.NeuralNetwork.HopfieldBoltzmannR

/-!
## Hopfield → Boltzmann/Gibbs bridge

This file specializes the generic finite-state Boltzmann/Gibbs construction in
`NeuralNetwork.NeuralNetwork.HopfieldBoltzmannR` to the concrete Hopfield network,
by providing the required `TwoState.EnergySpec'` (from `HopfieldEnergySpec.spec`).

With this, you can directly use:
- Boltzmann probabilities (`HopfieldBoltzmannR.P`)
- one-site Gibbs kernels (`HopfieldBoltzmannR.KbmMatrix`)
- random-scan Gibbs Markov chain matrices (`HopfieldBoltzmannR.randomScanMatrix`)
- MCMC stationary distribution API (`MCMC.Finite`), assuming irreducibility.
-/

namespace NeuralNetwork

open scoped BigOperators Temperature

namespace HopfieldGibbsBridge

open HopfieldEnergySpec

variable {R : Type} {U : Type}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

-- For Hopfield, the activation predicate is exactly `{σ_pos, σ_neg}`.
noncomputable instance : TwoState.TwoStateExclusiveR (NN := HopfieldNetwork R U) where
  pact_iff := by
    intro a
    -- for Hopfield, `pact a` is definitionally `a = 1 ∨ a = -1`
    simp [HopfieldNetwork, TwoStateNeuralNetwork.σ_pos, TwoStateNeuralNetwork.σ_neg]

-- Finite state space: a state is uniquely determined by a Boolean choice at each site.
noncomputable def stateEquivBool :
    (HopfieldNetwork R U).State ≃ (U → Bool) := by
  classical
  let σp : R := TwoStateNeuralNetwork.σ_pos (NN := HopfieldNetwork R U)
  let σn : R := TwoStateNeuralNetwork.σ_neg (NN := HopfieldNetwork R U)
  have hne : σp ≠ σn := TwoStateNeuralNetwork.h_pos_ne_neg (NN := HopfieldNetwork R U)
  refine
    { toFun := fun s u => if h : s.act u = σp then true else false
      invFun := fun b =>
        { act := fun u => if b u then σp else σn
          hp := by
            intro u
            -- `pact` for Hopfield is definitional: `a = 1 ∨ a = -1`
            -- and `σp = 1`, `σn = -1` by the TwoState instance.
            by_cases hb : b u
            · simp [hb, σp, σn, HopfieldNetwork, instTwoStateHopfield]
            · simp [hb, σp, σn, HopfieldNetwork, instTwoStateHopfield] }
      left_inv := by
        intro s
        ext u
        have hex : s.act u = σp ∨ s.act u = σn := by
          -- from exclusivity: `pact (s.act u)` implies `s.act u = σp ∨ σn`
          simpa [σp, σn] using
            (TwoState.TwoStateExclusiveR.pact_iff (NN := HopfieldNetwork R U) (a := s.act u)).1 (s.hp u)
        by_cases hpos : s.act u = σp
        · -- then `toFun` is true, `invFun` picks σp, which equals `s.act u`
          simp [σp, σn, hpos]
        · have hneg : s.act u = σn := by
            cases hex with
            | inl h => cases hpos h
            | inr h => exact h
          -- then `toFun` is false, `invFun` picks σn, which equals `s.act u`
          have ht : (if h : s.act u = σp then true else false) = false := by
            simp [hpos]
          -- expand `toFun`/`invFun` at `u` and finish with `hneg`
          simp [σp, σn, ht, hneg]; aesop
      right_inv := by
        intro b
        funext u
        by_cases hb : b u
        · -- act u = σp, test succeeds
          simp [σp, σn, hb]
        · -- act u = σn, test fails since σn ≠ σp
          have hne' : σn ≠ σp := by
            intro h; exact hne h.symm
          simp [σp, σn, hb, hne'] }

noncomputable instance : Fintype ( (HopfieldNetwork R U).State ) := by
  classical
  -- `U → Bool` is finite when `U` is finite.
  exact Fintype.ofEquiv (U → Bool) (stateEquivBool (R := R) (U := U)).symm

noncomputable instance : Nonempty ( (HopfieldNetwork R U).State ) := by
  classical
  refine ⟨(stateEquivBool (R := R) (U := U)).symm (fun _ => false)⟩

-- The Hopfield network as a two-state NN.
abbrev NN : NeuralNetwork R U R := HopfieldNetwork R U

-- Energy specification for Hopfield (proved in `HopfieldEnergySpec.lean`).
noncomputable def spec : TwoState.EnergySpec' (NN := HopfieldNetwork R U) :=
  HopfieldEnergySpec.spec (R := R) (U := U)

-- Re-export the canonical ensemble and Gibbs kernels from the generic construction.
namespace Boltz

open HopfieldBoltzmannR

variable [HasToReal R]

-- Canonical ensemble induced by Hopfield energy.
noncomputable def CEparams (p : Params (HopfieldNetwork R U)) :
    CanonicalEnsemble ((HopfieldNetwork R U).State) :=
  HopfieldBoltzmannR.CEparams (NN := (HopfieldNetwork R U)) (spec := spec (R := R) (U := U)) p

-- One-site Gibbs transition matrix at site `u`.
noncomputable def KbmMatrix
    (p : Params (HopfieldNetwork R U)) (T : Temperature) (f : R →+* ℝ) (u : U) :
    Matrix ((HopfieldNetwork R U).State) ((HopfieldNetwork R U).State) ℝ :=
  HopfieldBoltzmannR.KbmMatrix (NN := (HopfieldNetwork R U)) p T f u

-- Random-scan Gibbs transition matrix (uniform site).
noncomputable def randomScanMatrix
    (p : Params (HopfieldNetwork R U)) (T : Temperature) (f : R →+* ℝ) :
    Matrix ((HopfieldNetwork R U).State) ((HopfieldNetwork R U).State) ℝ :=
  HopfieldBoltzmannR.randomScanMatrix (NN := (HopfieldNetwork R U)) p T f

theorem randomScanMatrix_isStochastic
    (p : Params (HopfieldNetwork R U)) (T : Temperature) (f : R →+* ℝ) :
    MCMC.Finite.IsStochastic (randomScanMatrix (R := R) (U := U) p T f) := by
  classical
  simpa [randomScanMatrix, Boltz.randomScanMatrix] using
    HopfieldBoltzmannR.randomScanMatrix_isStochastic (NN := (HopfieldNetwork R U)) (p := p) (T := T) f

end Boltz

end HopfieldGibbsBridge

end NeuralNetwork
