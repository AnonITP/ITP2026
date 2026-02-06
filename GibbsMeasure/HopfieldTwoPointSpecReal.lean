import GibbsMeasure.HopfieldFromParamsReal
import GibbsMeasure.TwoPointBaseMeasureReal
import GibbsMeasure.Potential
import GibbsMeasure.Specification

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ENNReal.BigOperators

/-!
## Hopfield Georgii specification on real spins with two-point base measure

This file packages the *single-site reference measure* as the symmetric two-point measure on `ℝ`
(supported on `{±1}`), and builds the corresponding Georgii Gibbs specification from Hopfield
parameters.

The normalization/partition-function finiteness hypothesis `hZ` is kept explicit: in general this is
an analytic condition, but for the `{±1}` base measure and finite volumes it is expected to be
discharged by a dedicated lemma (next bridge step).
-/

namespace GibbsMeasure.Examples.HopfieldTwoPointSpecReal

open GibbsMeasure
open GibbsMeasure.Examples.HopfieldFromParamsReal
open MeasureTheory
open scoped BigOperators

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

private lemma twoPointMeasureReal_pair : twoPointMeasureReal ({(1 : ℝ), (-1 : ℝ)} : Set ℝ) = 1 := by
  classical
  -- unfold and compute on the pair set
  -- `twoPointMeasureReal` is a 1/2–1/2 mixture of diracs, and both atoms belong to `{1, -1}`.
  simp [GibbsMeasure.twoPointMeasureReal, ENNReal.inv_two_add_inv_two]

omit [DecidableEq U] [Fintype U] [Nonempty U] in
private lemma pi_twoPointMeasureReal_mem_pmOne (Λ : Finset U) :
    Measure.pi (fun _ : Λ => (twoPointMeasureReal : Measure ℝ))
        (Set.pi Set.univ (fun _ : Λ => ({(1 : ℝ), (-1 : ℝ)} : Set ℝ))) = 1 := by
  classical
  -- `pi_pi` over a finite index set
  haveI : ∀ _ : Λ, SigmaFinite (twoPointMeasureReal : Measure ℝ) := fun _ => inferInstance
  -- Evaluate the product measure on a rectangle
  simp [Measure.pi_pi, twoPointMeasureReal_pair, Finset.prod_const_one]

/-- For the two-point base measure, the Boltzmann partition function is always finite (never `⊤`). -/
lemma hZ_twoPointMeasureReal
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) :
    ∀ (Λ : Finset U) (η : U → ℝ),
      Specification.premodifierZ (S := U) (E := ℝ)
        twoPointMeasureReal
        (Potential.boltzmannWeight (Φ := hopfieldPotentialFromParamsR (U := U) p) β) Λ η ≠ ⊤ := by
  classical
  intro Λ η
  -- unfold `premodifierZ` and rewrite `isssd` as `map (juxt ...) (pi ν)`
  simp [Specification.premodifierZ, Specification.isssd_apply, Specification.isssdFun_apply]
  -- We are now integrating against `Measure.map (juxt Λ η) (Measure.pi (fun _ : Λ => ν))`.
  -- Pull back to the finite product space `Λ → ℝ`.
  have hmeas_f :
      Measurable (fun x : (U → ℝ) => Potential.boltzmannWeight
        (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ x) :=
    Potential.measurable_boltzmannWeight (S := U) (E := ℝ)
      (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ
  have hmeas_juxt : Measurable (juxt (Λ : Set U) η) :=
    (Measurable.juxt (Λ := (Λ : Set U)) (η := η) (𝓔 := inferInstance))
  -- rewrite lintegral over map
  have h_lintegral :
      (∫⁻ x, Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ x
        ∂Measure.map (juxt (Λ : Set U) η)
          (Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)))
        =
      ∫⁻ z, Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
        ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)) := by
    simpa using (MeasureTheory.lintegral_map (μ := Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ))
      (hf := hmeas_f) (hg := hmeas_juxt))
  -- Replace with the pulled-back integral.
  rw [h_lintegral]
  -- Let `A` be the finite set of configurations `z : Λ → ℝ` with coordinates in `{±1}`.
  let A : Set (Λ → ℝ) := Set.pi Set.univ (fun _ : Λ => ({(1 : ℝ), (-1 : ℝ)} : Set ℝ))
  have hA_finite : A.Finite := by
    -- finite product of finite sets
    have hfin : ∀ i : Λ, (({(1 : ℝ), (-1 : ℝ)} : Set ℝ)).Finite := fun _ => by
      simp [Set.finite_insert, Set.finite_singleton]
    simpa [A] using (Set.Finite.pi (ι := Λ) (t := fun _ : Λ => ({(1 : ℝ), (-1 : ℝ)} : Set ℝ)) hfin)
  have hA_meas : MeasurableSet A := by
    -- each coordinate set is measurable
    have hmeas : ∀ i : Λ, MeasurableSet (({(1 : ℝ), (-1 : ℝ)} : Set ℝ)) := fun _ => by
      -- `{1, -1} = insert 1 {-1}`
      simp
    have hcount : (Set.univ : Set Λ).Countable := Set.to_countable _
    simpa [A] using MeasurableSet.pi hcount (fun i _ => hmeas i)
  -- show the product measure gives mass 1 to `A`
  have hμA : (Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)) A = 1 := by
    simpa [A] using pi_twoPointMeasureReal_mem_pmOne (U := U) Λ
  -- hence the complement has measure 0, and restricting to `A` does not change the integral
  have hμAc : (Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)) Aᶜ = 0 := by
    let μ : Measure (Λ → ℝ) := Measure.pi (fun _ : Λ => (twoPointMeasureReal : Measure ℝ))
    haveI : IsProbabilityMeasure μ := by infer_instance
    -- for probability measures, `μ Aᶜ = 0 ↔ μ A = 1`
    simpa [μ] using (MeasureTheory.prob_compl_eq_zero_iff (μ := μ) hA_meas).2 (by simpa [μ] using hμA)
  -- Now integral over `A` is a finite sum, hence finite.
  have h_fin :
      (∫⁻ z, Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
        ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ))) ≠ ⊤ := by
    -- use `lintegral_add_compl` and `μ(Aᶜ)=0`
    -- reduce to integral over `A`
    have h_eq :
        (∫⁻ z, Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
          ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)))
          =
        ∫⁻ z in A, Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
          ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)) := by
      -- Split the integral over `A` and `Aᶜ`; the `Aᶜ` piece vanishes since `μ(Aᶜ)=0`.
      have hsplit :=
        (MeasureTheory.lintegral_add_compl
          (μ := Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ))
          (f := fun z => Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z))
          hA_meas)
      have hcompl :
          ∫⁻ z in Aᶜ, Potential.boltzmannWeight
              (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
            ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ))
            = 0 := by
        simp [Measure.restrict_eq_zero.2 hμAc]
      -- `hsplit : I_A + I_Ac = I`
      -- so `I = I_A` since `I_Ac = 0`
      simpa [hcompl] using hsplit.symm
    -- compute the restricted integral over a finite set using `lintegral_finset`
    let s : Finset (Λ → ℝ) := hA_finite.toFinset
    have hs : (s : Set (Λ → ℝ)) = A := by
      simp [s]
    -- show each summand is < ⊤, hence the sum is < ⊤
    have hsum_lt :
        (∑ z ∈ s,
          (Potential.boltzmannWeight
            (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)) *
              (Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)) {z}) < ⊤ := by
      refine (ENNReal.sum_lt_top).2 ?_
      intro z hz
      have : Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z) ≠ ⊤ := by
        -- `boltzmannWeight` is an `ofReal`, hence never top
        simp [Potential.boltzmannWeight]
      -- product of a finite value with a finite mass is finite
      exact ENNReal.mul_lt_top this.lt_top (measure_lt_top _ _)
    -- conclude `lintegral < ⊤`
    have : (∫⁻ z in A, Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
        ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ))) < ⊤ := by
      haveI : MeasurableSingletonClass (Λ → ℝ) := by infer_instance
      -- rewrite `A` via `s` and use `lintegral_finset`
      have hlin :
          (∫⁻ z in A,
              Potential.boltzmannWeight
                (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
            ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)))
            =
            ∑ z ∈ s,
              Potential.boltzmannWeight
                  (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z) *
                (Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)) {z} := by
        simpa [hs] using
          (MeasureTheory.lintegral_finset
            (μ := Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ))
            s
            (fun z =>
              Potential.boltzmannWeight
                (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)))
      -- finiteness follows from the explicit finite sum bound
      have : (∑ z ∈ s,
          Potential.boltzmannWeight
              (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z) *
            (Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ)) {z}) < ⊤ := hsum_lt
      simpa [hlin] using this
    -- use the equality to transfer finiteness
    have hA_lt : (∫⁻ z in A, Potential.boltzmannWeight
          (Φ := hopfieldPotentialFromParamsR (U := U) p) β Λ (juxt (Λ : Set U) η z)
        ∂(Measure.pi fun _ : Λ => (twoPointMeasureReal : Measure ℝ))) ≠ ⊤ :=
      ne_of_lt this
    -- now apply `h_eq`
    simpa [h_eq] using hA_lt
  exact h_fin

noncomputable def hopfieldSpecificationTwoPointFromParamsR
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ)
    : Specification U ℝ :=
  hopfieldSpecificationFromParamsR (U := U) p β twoPointMeasureReal (hZ_twoPointMeasureReal (U := U) p β)

end

end GibbsMeasure.Examples.HopfieldTwoPointSpecReal
