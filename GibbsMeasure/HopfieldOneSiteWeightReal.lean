import GibbsMeasure.HopfieldTwoPointSpecReal
import GibbsMeasure.Potential
import GibbsMeasure.Specification

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.BigOperators

/-!
## One-site finite-volume formulas for the `{±1}` base measure (real spins)

This file is the first “DLR ↔ SOTA update” bridge layer:

- for volume `Λ = {u}`, the Georgii partition function is an explicit two-point sum;
- the modified one-site kernel assigns the event `{σ | σ u = 1}` the usual weight ratio
  `w(1) / (w(1) + w(-1))`.

The next file will identify the ratio `w(1)/w(-1)` with `exp(2β * localField)` using the Hopfield
Hamiltonian identity.
-/

namespace GibbsMeasure.Examples.HopfieldOneSiteWeightReal

open GibbsMeasure
open GibbsMeasure.Examples.HopfieldFromParamsReal
open GibbsMeasure.Examples.HopfieldTwoPointSpecReal
open MeasureTheory
open scoped BigOperators ENNReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

private def oneSite (u : U) : Finset U := ({u} : Finset U)

/-- The two-point integral against `twoPointMeasureReal` is a 1/2–1/2 sum. -/
private lemma lintegral_twoPointMeasureReal (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x ∂twoPointMeasureReal
      = (2⁻¹ : ℝ≥0∞) * f (1 : ℝ) + (2⁻¹ : ℝ≥0∞) * f (-1 : ℝ) := by
  classical
  -- unfold and use `lintegral_{add,smul,dirac}`
  simp [twoPointMeasureReal, lintegral_add_measure, lintegral_smul_measure]

/-- In volume `{u}`, the partition function is the average of the two Boltzmann weights. -/
lemma partitionFunction_oneSite
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) :
    Potential.partitionFunction (S := U) (E := ℝ) (Φ := hopfieldPotentialFromParamsR (U := U) p)
        β twoPointMeasureReal (oneSite (u := u)) η
      =
      (2⁻¹ : ℝ≥0∞) *
          Potential.boltzmannWeight (Φ := hopfieldPotentialFromParamsR (U := U) p) β (oneSite (u := u))
            (Function.update η u (1 : ℝ))
        +
        (2⁻¹ : ℝ≥0∞) *
          Potential.boltzmannWeight (Φ := hopfieldPotentialFromParamsR (U := U) p) β (oneSite (u := u))
            (Function.update η u (-1 : ℝ)) := by
  classical
  -- expand `partitionFunction = premodifierZ = ∫ boltzmannWeight d(isssd ...)`
  simp [Potential.partitionFunction, Specification.premodifierZ, Specification.isssd_apply,
    Specification.isssdFun_apply, oneSite]
  -- pull back to the one-coordinate product space via `lintegral_map`
  have hmeas :
      Measurable
        (Potential.boltzmannWeight (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)) :=
    Potential.measurable_boltzmannWeight (S := U) (E := ℝ)
      (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
  have hjuxt : Measurable (juxt (Λ := (({u} : Finset U) : Set U)) η) :=
    (Measurable.juxt (Λ := (({u} : Finset U) : Set U)) (η := η) (𝓔 := inferInstance))
  -- rewrite via `lintegral_map`
  rw [MeasureTheory.lintegral_map (hf := hmeas) (hg := hjuxt)]
  -- identify the one-coordinate product measure with `twoPointMeasureReal`
  -- via the measurable equivalence `piUnique` on the singleton index type.
  classical
  let ι := (↥({u} : Finset U))
  let i0 : ι := ⟨u, by simp⟩
  haveI : Unique ι :=
    ⟨⟨i0⟩, by
      intro i
      -- reduce to the underlying value in `U`
      cases i with
      | mk x hx =>
          -- `x ∈ {u}` forces `x = u`
          have hx' : x = u := by simpa using (Finset.mem_singleton.1 hx)
          subst hx'
          -- proof-irrelevance closes the subtype equality
          rfl⟩
  let e : (ι → ℝ) ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : ι => ℝ)
  have hmap :
      Measure.map e (Measure.pi fun _ : ι => (twoPointMeasureReal : Measure ℝ))
        = twoPointMeasureReal := by
    simpa using
      (measurePreserving_piUnique (X := fun _ : ι => ℝ) (μ := fun _ : ι => (twoPointMeasureReal : Measure ℝ))).map_eq
  have hback :
      Measure.map e.symm twoPointMeasureReal
        = Measure.pi (fun _ : ι => (twoPointMeasureReal : Measure ℝ)) := by
    -- invert `hmap`
    have := congrArg (Measure.map e.symm) hmap
    -- `map e.symm (map e μ) = μ`
    simpa [MeasurableEquiv.map_map_symm] using this.symm
  -- measurability of the pulled-back integrand on the one-coordinate configuration space
  have hfζ :
      Measurable (fun ζ : ι → ℝ =>
        Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
          (juxt (Λ := (({u} : Finset U) : Set U)) η ζ)) := by
    exact hmeas.comp (Measurable.juxt (Λ := (({u} : Finset U) : Set U)) (η := η) (𝓔 := inferInstance))
  have hlin :
      (∫⁻ ζ,
          Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
            (juxt (Λ := (({u} : Finset U) : Set U)) η ζ)
        ∂(Measure.pi fun _ : ι => (twoPointMeasureReal : Measure ℝ)))
        =
      ∫⁻ r,
          Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
            (juxt (Λ := (({u} : Finset U) : Set U)) η (e.symm r))
        ∂twoPointMeasureReal := by
    -- rewrite LHS using `hback` then apply `lintegral_map`
    calc
      (∫⁻ ζ,
          Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
            (juxt (Λ := (({u} : Finset U) : Set U)) η ζ)
        ∂(Measure.pi fun _ : ι => (twoPointMeasureReal : Measure ℝ)))
          =
        ∫⁻ ζ,
          Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
            (juxt (Λ := (({u} : Finset U) : Set U)) η ζ)
        ∂(Measure.map e.symm twoPointMeasureReal) := by simp [hback]
      _ =
        ∫⁻ r,
          Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
            (juxt (Λ := (({u} : Finset U) : Set U)) η (e.symm r))
        ∂twoPointMeasureReal := by
            simpa using
              (MeasureTheory.lintegral_map (μ := twoPointMeasureReal) (hf := hfζ) (hg := e.symm.measurable))
  -- `e.symm` is `uniqueElim`, so the only coordinate is `r`.
  have hjuxt_update :
      ∀ r : ℝ,
        juxt (Λ := (({u} : Finset U) : Set U)) η (e.symm r) = Function.update η u r := by
    intro r
    funext x
    by_cases hx : x = u
    · subst hx
      simp [juxt, e, Function.update]
    · have : x ∉ ({u} : Finset U) := by simpa using hx
      simp [juxt, hx, Function.update]
  -- Finish by evaluating the two-point integral.
  calc
    (∫⁻ ζ,
        Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
          (juxt (Λ := (({u} : Finset U) : Set U)) η ζ)
      ∂(Measure.pi fun _ : ι => (twoPointMeasureReal : Measure ℝ)))
        =
      ∫⁻ r,
        Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
          (juxt (Λ := (({u} : Finset U) : Set U)) η (e.symm r))
      ∂twoPointMeasureReal := hlin
    _ =
      (2⁻¹ : ℝ≥0∞) *
          Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
            (Function.update η u (1 : ℝ))
        +
        (2⁻¹ : ℝ≥0∞) *
          Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β ({u} : Finset U)
            (Function.update η u (-1 : ℝ)) := by
          -- apply the two-point lintegral formula and rewrite `juxt` as `Function.update`
          simp [lintegral_twoPointMeasureReal, hjuxt_update]

end

end GibbsMeasure.Examples.HopfieldOneSiteWeightReal
