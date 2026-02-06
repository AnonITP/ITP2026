import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Real

/-!
## Two-point base measure on `ℝ` (spins `±1`)

This file defines the canonical probability measure on `ℝ` supported on `{1, -1}`:
\[
  \nu_{\pm} = \tfrac12 \delta_{1} + \tfrac12 \delta_{-1}.
\]

It is the natural single-site reference measure for two-state (Ising/Hopfield) models when we
represent spins as reals `±1`.
-/

open scoped ENNReal
open MeasureTheory

namespace GibbsMeasure

noncomputable section

/-- The symmetric two-point probability measure on `ℝ` supported on `{1, -1}`. -/
noncomputable def twoPointMeasureReal : Measure ℝ :=
  (ENNReal.ofReal (1 / 2 : ℝ)) • Measure.dirac (1 : ℝ) +
    (ENNReal.ofReal (1 / 2 : ℝ)) • Measure.dirac (-1 : ℝ)

instance : IsProbabilityMeasure twoPointMeasureReal := by
  classical
  refine ⟨?_⟩
  -- compute total mass
  -- `μ univ = 1/2 + 1/2 = 1`
  simp [twoPointMeasureReal, Measure.add_apply, Measure.smul_apply,
    ENNReal.inv_two_add_inv_two]

@[simp] lemma twoPointMeasureReal_apply_singleton_one :
    twoPointMeasureReal ({(1 : ℝ)} : Set ℝ) = (2⁻¹ : ℝ≥0∞) := by
  classical
  -- direct computation from the definition
  by_cases h : (1 : ℝ) = -1
  · have : (2 : ℝ) = 0 := by linarith
    exact (two_ne_zero this).elim
  · simp [twoPointMeasureReal, h]

@[simp] lemma twoPointMeasureReal_apply_singleton_negOne :
    twoPointMeasureReal ({(-1 : ℝ)} : Set ℝ) = (2⁻¹ : ℝ≥0∞) := by
  classical
  by_cases h : (-1 : ℝ) = 1
  · have : (2 : ℝ) = 0 := by linarith
    exact (two_ne_zero this).elim
  · simp [twoPointMeasureReal, h]

end

end GibbsMeasure
