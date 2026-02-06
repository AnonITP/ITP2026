import GibbsMeasure.HopfieldFromParamsReal
import GibbsMeasure.HopfieldEnergyBridgeReal

/-!
## Local flip identities for Hopfield potential atoms (real spins)

This file proves *atomic* Hamiltonian flip identities for the Georgii potential
`hopfieldPotentialFromParamsR` at:

- singleton support `{u}`
- pair support `{u,v}`

These are purely deterministic identities for general configurations `η : U → ℝ`. They are the
building blocks for the full one-site Hamiltonian identity (volume `{u}`) and the logistic update
bridge.
-/

namespace GibbsMeasure.Examples.HopfieldLocalFlipAtomsReal

open GibbsMeasure.Examples.HopfieldFromParamsReal
open GibbsMeasure.Examples.HopfieldEnergyBridgeReal
open scoped BigOperators

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

/-- Flip identity on the singleton potential `{u}`. -/
lemma singleton_flip
    (p : Params (HopfieldNetwork ℝ U)) (u : U) (η : U → ℝ) :
    hopfieldPotentialFromParamsR (U := U) p ({u} : Finset U) (Function.update η u (1 : ℝ))
      -
    hopfieldPotentialFromParamsR (U := U) p ({u} : Finset U) (Function.update η u (-1 : ℝ))
      =
      (2 : ℝ) * θu (U := U) p u := by
  classical
  -- evaluate via the singleton atom lemma
  simp [hopfieldPotentialFromParamsR_singleton (U := U) (p := p) (i := u),
    Function.update]
  ring

/-- Flip identity on the pair potential `{u,v}` (uses symmetry of Hopfield weights). -/
lemma pair_flip
    (p : Params (HopfieldNetwork ℝ U)) {u v : U} (huv : u ≠ v) (η : U → ℝ) :
    hopfieldPotentialFromParamsR (U := U) p ({u, v} : Finset U) (Function.update η u (1 : ℝ))
      -
    hopfieldPotentialFromParamsR (U := U) p ({u, v} : Finset U) (Function.update η u (-1 : ℝ))
      =
      - (2 : ℝ) * (p.w u v) * (η v) := by
  classical
  have hwSymm : p.w.IsSymm := by
    -- for HopfieldNetwork, `pw w := w.IsSymm`
    simpa using (p.hw' : p.w.IsSymm)
  have hwuv : p.w v u = p.w u v := by
    simpa using (Matrix.IsSymm.apply hwSymm u v)
  -- evaluate the pair atom, then simplify
  have hpair_pos :=
    hopfieldPotentialFromParamsR_pair (U := U) (p := p) (i := u) (j := v) huv
      (η := Function.update η u (1 : ℝ))
  have hpair_neg :=
    hopfieldPotentialFromParamsR_pair (U := U) (p := p) (i := u) (j := v) huv
      (η := Function.update η u (-1 : ℝ))
  -- compute the difference; only `η u` changes
  -- (we keep the algebra explicit to avoid simp blowups)
  -- First rewrite both sides using the pair atom formula.
  rw [hpair_pos, hpair_neg]
  -- Now simplify the updates: `update η u a u = a` and (since `v ≠ u`) `update η u a v = η v`.
  have hvu : v ≠ u := huv.symm
  simp [Function.update, hvu, hwuv]
  ring_nf

end

end GibbsMeasure.Examples.HopfieldLocalFlipAtomsReal
