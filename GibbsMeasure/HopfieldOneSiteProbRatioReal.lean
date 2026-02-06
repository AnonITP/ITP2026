import GibbsMeasure.HopfieldOneSiteWeightReal
import GibbsMeasure.HopfieldOneSiteHamiltonianFlipReal
import GibbsMeasure.TwoPointBaseMeasureReal

import GibbsMeasure.Potential
import GibbsMeasure.Specification

import NeuralNetwork.NeuralNetwork.TwoState
import NeuralNetwork.NeuralNetwork.HopfieldEnergySpec

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
## One-site probability ratio for the `{±1}` base measure (real spins)

This file computes the *finite-volume one-site distribution* in volume `{u}`:

If we consider the base measure `ν±` on the single spin and weight it by the one-site Boltzmann
factor, the resulting probability that the updated spin is `+1` is exactly the ratio
\[
  \frac{w(1)}{w(1) + w(-1)}.
\]

This is the canonical “DLR measure-theoretic half” before rewriting the ratio via the Hopfield
Hamiltonian identity (local field / logistic formula).
-/

namespace GibbsMeasure.Examples.HopfieldOneSiteProbRatioReal

open GibbsMeasure
open GibbsMeasure.Examples.HopfieldFromParamsReal
open GibbsMeasure.Examples.HopfieldOneSiteWeightReal
open GibbsMeasure.Examples.HopfieldOneSiteHamiltonianFlipReal
open MeasureTheory
open TwoState
open scoped BigOperators ENNReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

/-- The singleton volume `{u}` used for one-site conditionals. -/
abbrev oneSite (u : U) : Finset U := ({u} : Finset U)

/-- Hopfield Georgii potential from Hopfield parameters (real spins). -/
abbrev Φ (p : Params (HopfieldNetwork ℝ U)) : Potential U ℝ :=
  hopfieldPotentialFromParamsR (U := U) p

private instance (p : Params (HopfieldNetwork ℝ U)) : Potential.IsFinitary (Φ (U := U) p) := by
  simpa [Φ] using (inferInstance : Potential.IsFinitary (hopfieldPotentialFromParamsR (U := U) p))

private instance (p : Params (HopfieldNetwork ℝ U)) : Potential.IsPotential (Φ (U := U) p) := by
  simpa [Φ] using (inferInstance : Potential.IsPotential (hopfieldPotentialFromParamsR (U := U) p))

/-! ### Local Boltzmann weights / partition function -/

/-- One-site Boltzmann weight \(w(a)\) for `a ∈ {±1}` (as `ℝ≥0∞`). -/
def w (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) (a : ℝ) : ℝ≥0∞ :=
  Potential.boltzmannWeight (Φ := Φ (U := U) p) β (oneSite (u := u)) (Function.update η u a)

/-- One-site partition function \(Z\) in volume `{u}` (as `ℝ≥0∞`). -/
def Z (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) : ℝ≥0∞ :=
  Potential.partitionFunction (S := U) (E := ℝ) (Φ := Φ (U := U) p) β twoPointMeasureReal
    (oneSite (u := u)) η

private lemma Z_eq_half_sum (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) :
    Z (U := U) p β u η =
      (2⁻¹ : ℝ≥0∞) * w (U := U) p β u η (1 : ℝ) +
      (2⁻¹ : ℝ≥0∞) * w (U := U) p β u η (-1 : ℝ) := by
  simpa [Z, w, Φ, oneSite] using
    (partitionFunction_oneSite (U := U) (p := p) (β := β) (u := u) (η := η))

/-- The one-site `{±1}`-base distribution on the updated spin (as a measure on `ℝ`). -/
noncomputable def oneSiteSpinLaw
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) : Measure ℝ :=
  twoPointMeasureReal.withDensity fun a => w (U := U) p β u η a / Z (U := U) p β u η

lemma oneSiteSpinLaw_apply_one
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) :
    oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ)
      =
      w (U := U) p β u η (1 : ℝ) /
        (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ)) := by
  classical
  -- expand the measure on the singleton using `withDensity_apply` and `lintegral_singleton`
  have hmeas : MeasurableSet ({(1 : ℝ)} : Set ℝ) := measurableSet_singleton _
  have hZ : Z (U := U) p β u η =
      (2⁻¹ : ℝ≥0∞) * w (U := U) p β u η (1 : ℝ) +
      (2⁻¹ : ℝ≥0∞) * w (U := U) p β u η (-1 : ℝ) :=
    Z_eq_half_sum (U := U) (p := p) (β := β) (u := u) (η := η)
  -- compute
  -- First compute it as `(1/2) * w(1) / Z`, then rewrite `Z` and cancel the `1/2`.
  have hcalc :
      oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ)
        = (2⁻¹ : ℝ≥0∞) * (w (U := U) p β u η (1 : ℝ) / Z (U := U) p β u η) := by
    -- withDensity on a singleton reduces to the density at the point times the base mass
    simp [oneSiteSpinLaw, MeasureTheory.withDensity_apply, hmeas,
      GibbsMeasure.twoPointMeasureReal_apply_singleton_one, div_eq_mul_inv]
  -- Now use the explicit `Z` formula and simplify.
  -- `Z = 1/2*w1 + 1/2*w-1`, hence `1/2 * (w1/Z) = w1/(w1+w-1)`.
  -- We do the cancellation by factoring out `2⁻¹` in the denominator.
  have hZ' :
      Z (U := U) p β u η = (2⁻¹ : ℝ≥0∞) * (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ)) := by
    -- factor `2⁻¹` out of the sum
    simp [mul_add, hZ]
  -- Conclude: rewrite as `(c*w1)/(c*(w1+w2))` and use `ENNReal.mul_div_mul_left`.
  have h2ne0 : (2⁻¹ : ℝ≥0∞) ≠ 0 := by
    simp
  have h2netop : (2⁻¹ : ℝ≥0∞) ≠ ⊤ := by simp
  calc
    oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ)
        = (2⁻¹ : ℝ≥0∞) * (w (U := U) p β u η (1 : ℝ) / Z (U := U) p β u η) := hcalc
    _ = (2⁻¹ : ℝ≥0∞) * (w (U := U) p β u η (1 : ℝ) /
            ((2⁻¹ : ℝ≥0∞) * (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ)))) := by
          simp [hZ']
    _ = ((2⁻¹ : ℝ≥0∞) * w (U := U) p β u η (1 : ℝ)) /
            ((2⁻¹ : ℝ≥0∞) * (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ))) := by
          simp [div_eq_mul_inv, mul_assoc]
    _ =
        w (U := U) p β u η (1 : ℝ) /
          (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ)) := by
          -- cancel the common factor `2⁻¹`
          simpa using
            (ENNReal.mul_div_mul_left
              (a := w (U := U) p β u η (1 : ℝ))
              (b := (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ)))
              (c := (2⁻¹ : ℝ≥0∞)) h2ne0 h2netop)

/-- Rewriting the one-site probability in **logistic form**, using the one-site Hamiltonian identity. -/
lemma oneSiteSpinLaw_apply_one_toReal_eq_logisticProb
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) :
    ENNReal.toReal (oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ))
      =
      logisticProb (2 * β * (field (U := U) p η u - HopfieldFromParamsReal.θu (U := U) p u)) := by
  classical
  -- start from the ratio formula
  have hprob :=
    oneSiteSpinLaw_apply_one (U := U) (p := p) (β := β) (u := u) (η := η)
  -- abbreviate the two Hamiltonians
  set Hpos : ℝ :=
      Potential.interactingHamiltonian (Φ := Φ (U := U) p) (oneSite (u := u))
        (Function.update η u (1 : ℝ)) with hHpos
  set Hneg : ℝ :=
      Potential.interactingHamiltonian (Φ := Φ (U := U) p) (oneSite (u := u))
        (Function.update η u (-1 : ℝ)) with hHneg
  have hwpos :
      w (U := U) p β u η (1 : ℝ) = ENNReal.ofReal (Real.exp (-(β * Hpos))) := by
    have : -β * Hpos = -(β * Hpos) := by ring
    simp [w, Φ, oneSite, Potential.boltzmannWeight, hHpos]
  have hwneg :
      w (U := U) p β u η (-1 : ℝ) = ENNReal.ofReal (Real.exp (-(β * Hneg))) := by
    have : -β * Hneg = -(β * Hneg) := by ring
    simp [w, Φ, oneSite, Potential.boltzmannWeight, hHneg]
  -- `Hpos - Hneg = 2*θu - 2*field` (from the deterministic one-site Hamiltonian theorem)
  have hflip :
      Hpos - Hneg =
        (2 : ℝ) * HopfieldFromParamsReal.θu (U := U) p u - (2 : ℝ) * field (U := U) p η u := by
    -- unfold and use the theorem
    -- (note: this theorem is in the `HopfieldOneSiteHamiltonianFlipReal` namespace we opened)
    simpa [Hpos, Hneg, Φ, oneSite] using
      (interactingHamiltonian_oneSite_flip (U := U) (p := p) (u := u) (η := η))
  have hΔ : Hneg - Hpos = (2 : ℝ) * (field (U := U) p η u - θu (U := U) p u) := by
    -- rearrange `hflip`
    have : Hneg - Hpos = - (Hpos - Hneg) := by ring
    rw [this, hflip]
    ring
  -- convert the ENNReal ratio to a real ratio of exponentials
  have htoReal :
      ENNReal.toReal
          (w (U := U) p β u η (1 : ℝ) /
            (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ)))
        =
      (Real.exp (-(β * Hpos))) / (Real.exp (-(β * Hpos)) + Real.exp (-(β * Hneg))) := by
    -- rewrite weights as `ofReal exp`, then use `toReal_div`/`toReal_add`.
    have hpos_nonneg : 0 ≤ Real.exp (-(β * Hpos)) := (Real.exp_pos _).le
    have hneg_nonneg : 0 ≤ Real.exp (-(β * Hneg)) := (Real.exp_pos _).le
    -- (we keep this as an explicit `rw` + `simp` to ensure the nonneg proofs are used)
    rw [hwpos, hwneg]
    simp [ENNReal.toReal_div, ENNReal.toReal_add,
      ENNReal.toReal_ofReal hpos_nonneg, ENNReal.toReal_ofReal hneg_nonneg]
  -- finish: logistic normalization via dividing numerator+denominator by `exp (-(β*Hpos))`
  have hexp :
      Real.exp (-(β * Hneg)) =
        Real.exp (-(β * Hpos)) * Real.exp (-(β * (Hneg - Hpos))) := by
    have : -(β * Hneg) = (-(β * Hpos)) + (-(β * (Hneg - Hpos))) := by ring
    calc
      Real.exp (-(β * Hneg))
          = Real.exp ((-(β * Hpos)) + (-(β * (Hneg - Hpos)))) := by simp [this]
      _ = Real.exp (-(β * Hpos)) * Real.exp (-(β * (Hneg - Hpos))) := by
            simp [Real.exp_add]
  -- now compute
  have hlog :
      (Real.exp (-(β * Hpos))) / (Real.exp (-(β * Hpos)) + Real.exp (-(β * Hneg)))
        =
      logisticProb (β * (Hneg - Hpos)) := by
    have hpos_ne : Real.exp (-(β * Hpos)) ≠ 0 := Real.exp_ne_zero _
    -- substitute `hexp` and cancel the positive factor `exp(-β*Hpos)`
    calc
      (Real.exp (-(β * Hpos))) / (Real.exp (-(β * Hpos)) + Real.exp (-(β * Hneg)))
          =
        (Real.exp (-(β * Hpos))) /
          (Real.exp (-(β * Hpos)) + Real.exp (-(β * Hpos)) * Real.exp (-(β * (Hneg - Hpos)))) := by
            simp [hexp]
      _ =
        (Real.exp (-(β * Hpos))) /
          (Real.exp (-(β * Hpos)) * (1 + Real.exp (-(β * (Hneg - Hpos))))) := by
            ring
      _ = 1 / (1 + Real.exp (-(β * (Hneg - Hpos)))) := by
            field_simp [hpos_ne]
      _ = logisticProb (β * (Hneg - Hpos)) := by
            simp [logisticProb]
  -- assemble everything and substitute `Hneg - Hpos`
  calc
    ENNReal.toReal (oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ))
        =
      ENNReal.toReal
          (w (U := U) p β u η (1 : ℝ) /
            (w (U := U) p β u η (1 : ℝ) + w (U := U) p β u η (-1 : ℝ))) := by
          simp [hprob]
    _ = (Real.exp (-(β * Hpos))) / (Real.exp (-(β * Hpos)) + Real.exp (-(β * Hneg))) := htoReal
    _ = logisticProb (β * (Hneg - Hpos)) := hlog
    _ = logisticProb (2 * β * (field (U := U) p η u - HopfieldFromParamsReal.θu (U := U) p u)) := by
          -- replace the argument using `hΔ` and normalize the scalar multiplication
          have harg :
              β * (Hneg - Hpos) =
                2 * β * (field (U := U) p η u - HopfieldFromParamsReal.θu (U := U) p u) := by
            rw [hΔ]
            ring
          simp [harg]

/-- Specialization of the logistic-form lemma to Hopfield **states** (spins in `{±1}`),
rewritten in terms of the SOTA `HopfieldEnergySpec.localField`. -/
lemma oneSiteSpinLaw_apply_one_toReal_eq_logisticProb_localField
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (s : (HopfieldNetwork ℝ U).State) :
    ENNReal.toReal (oneSiteSpinLaw (U := U) p β u s.act ({(1 : ℝ)} : Set ℝ))
      =
      logisticProb (2 * β * (NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u)) := by
  classical
  -- start from the general `η` logistic lemma
  have h :=
    oneSiteSpinLaw_apply_one_toReal_eq_logisticProb (U := U) (p := p) (β := β) (u := u) (η := s.act)
  -- rewrite `field - θu` into `localField` using HopfieldEnergySpec’s lemma
  -- First: identify the two “field” sums (erase vs `{v | v ≠ u}`).
  have hfield :
      field (U := U) p s.act u =
        NeuralNetwork.HopfieldEnergySpec.field (R := ℝ) (U := U) p s u := by
    classical
    -- HopfieldEnergySpec.field sums over `{v : U | v ≠ u}`; rewrite that finset to `univ.erase u`.
    have hindex : ({v : U | v ≠ u} : Finset U) = Finset.univ.erase u := by
      ext v
      simp [Finset.mem_erase]
    simp [NeuralNetwork.HopfieldEnergySpec.field, field, hindex]
  have hθ :
      HopfieldFromParamsReal.θu (U := U) p u =
        NeuralNetwork.HopfieldEnergySpec.θu (R := ℝ) (U := U) p u := by
    -- both are the “0th coordinate” of the 1-vector threshold
    simp [HopfieldFromParamsReal.θu, NeuralNetwork.HopfieldEnergySpec.θu, θ', TwoState.fin0]
  have hlocal :
      field (U := U) p s.act u - HopfieldFromParamsReal.θu (U := U) p u =
        NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u := by
    -- HopfieldEnergySpec: `localField = field - θu`
    -- (rewrite the HopfieldEnergySpec field/θu into our versions)
    have :=
      (NeuralNetwork.HopfieldEnergySpec.localField_eq_field_sub_θu
        (R := ℝ) (U := U) (p := p) (s := s) (u := u))
    -- `this : localField = field - θu`; rearrange
    -- then rewrite `field`/`θu` using `hfield`/`hθ`.
    -- Note: `sub_eq_add_neg` normalization differs; keep it direct.
    -- From `localField = fieldNN - θuNN`, we get `fieldNN - θuNN = localField`.
    simpa [hfield, hθ] using this.symm
  -- finish by rewriting the logistic argument (avoid `simp` expansion/heartbeats)
  calc
    ENNReal.toReal (oneSiteSpinLaw (U := U) p β u s.act ({(1 : ℝ)} : Set ℝ))
        = logisticProb (2 * β * (field (U := U) p s.act u - HopfieldFromParamsReal.θu (U := U) p u)) := h
    _ = logisticProb (2 * β * (NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u)) := by
        -- rewrite the argument using `hlocal`
        exact congrArg (fun x => logisticProb (2 * β * x)) hlocal

end

end GibbsMeasure.Examples.HopfieldOneSiteProbRatioReal
