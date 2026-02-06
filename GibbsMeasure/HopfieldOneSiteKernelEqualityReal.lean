import GibbsMeasure.HopfieldOneSiteProbRatioReal
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
## One-site kernel equality (real spins): explicit two-point mixture form

This file packages the one-site conditional law in volume `{u}` (for the `{±1}` base measure)
as an explicit **two-atom measure**.

Combined with
`GibbsMeasure.Examples.HopfieldOneSiteProbRatioReal.oneSiteSpinLaw_apply_one_toReal_eq_logisticProb_localField`,
this identifies the Georgii/DLR one-site kernel with the SOTA logistic parameter coming from
`NeuralNetwork.HopfieldEnergySpec`.
-/

namespace GibbsMeasure.Examples.HopfieldOneSiteKernelEqualityReal

open GibbsMeasure
open GibbsMeasure.Examples.HopfieldFromParamsReal
open GibbsMeasure.Examples.HopfieldOneSiteProbRatioReal
open MeasureTheory
open scoped BigOperators ENNReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

namespace OneSite

/-- The explicit two-point mixture measure with masses `p1` at `+1` and `pneg` at `-1`. -/
noncomputable def twoPointMixture (p1 pneg : ℝ≥0∞) : Measure ℝ :=
  p1 • Measure.dirac (1 : ℝ) + pneg • Measure.dirac (-1 : ℝ)

@[simp] lemma twoPointMixture_apply_singleton_one (p1 pneg : ℝ≥0∞) :
    twoPointMixture p1 pneg ({(1 : ℝ)} : Set ℝ) = p1 := by
  classical
  have h : (-1 : ℝ) ∉ ({(1 : ℝ)} : Set ℝ) := by
    simp [Set.mem_singleton_iff, show (-1 : ℝ) ≠ 1 by norm_num]
  simp [twoPointMixture, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, h]

@[simp] lemma twoPointMixture_apply_singleton_negOne (p1 pneg : ℝ≥0∞) :
    twoPointMixture p1 pneg ({(-1 : ℝ)} : Set ℝ) = pneg := by
  classical
  have h : (1 : ℝ) ∉ ({(-1 : ℝ)} : Set ℝ) := by
    simp [Set.mem_singleton_iff, show (1 : ℝ) ≠ -1 by norm_num]
  simp [twoPointMixture, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, h]

/-- `oneSiteSpinLaw` is a two-point mixture measure (no longer “hidden” inside `withDensity`). -/
theorem oneSiteSpinLaw_eq_twoPointMixture
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (u : U) (η : U → ℝ) :
    HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η =
      twoPointMixture
        (HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ))
        (HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η ({(-1 : ℝ)} : Set ℝ)) := by
  classical
  let c : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞)
  let f : ℝ → ℝ≥0∞ :=
    fun a => HopfieldOneSiteProbRatioReal.w (U := U) p β u η a /
      HopfieldOneSiteProbRatioReal.Z (U := U) p β u η
  have hspin :
      HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η =
        (c * f (1 : ℝ)) • Measure.dirac (1 : ℝ) +
          (c * f (-1 : ℝ)) • Measure.dirac (-1 : ℝ) := by
    -- unfold `oneSiteSpinLaw`, then compute `twoPointMeasureReal.withDensity f`
    -- by pushing `withDensity` through `+` and `•`, and evaluating on `dirac`.
    have :
        GibbsMeasure.twoPointMeasureReal.withDensity f =
          (c * f (1 : ℝ)) • Measure.dirac (1 : ℝ) +
            (c * f (-1 : ℝ)) • Measure.dirac (-1 : ℝ) := by
      -- `twoPointMeasureReal = c•δ₁ + c•δ₋₁`
      -- `(μ+ν).withDensity f = μ.withDensity f + ν.withDensity f`
      -- `(r•μ).withDensity f = r•(μ.withDensity f)`
      -- `(dirac a).withDensity f = f a • dirac a`
      simp [GibbsMeasure.twoPointMeasureReal, c, f,
        MeasureTheory.withDensity_add_measure, MeasureTheory.withDensity_smul_measure,
        MeasureTheory.dirac_withDensity, smul_smul, mul_assoc, mul_left_comm, mul_comm,
        add_assoc, add_left_comm, add_comm]
    simpa [HopfieldOneSiteProbRatioReal.oneSiteSpinLaw, f] using this
  have hone :
      HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ) =
        c * f (1 : ℝ) := by
    have hne : (-1 : ℝ) ∉ ({(1 : ℝ)} : Set ℝ) := by
      simp [Set.mem_singleton_iff, show (-1 : ℝ) ≠ 1 by norm_num]
    simpa [hspin, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, hne, c, f]
  have hneg :
      HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η ({(-1 : ℝ)} : Set ℝ) =
        c * f (-1 : ℝ) := by
    have hne : (1 : ℝ) ∉ ({(-1 : ℝ)} : Set ℝ) := by
      simp [Set.mem_singleton_iff, show (1 : ℝ) ≠ -1 by norm_num]
    simpa [hspin, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, hne, c, f]
  -- rewrite `hspin` as a `twoPointMixture` with singleton masses (avoid `simp` producing `Pi.single`)
  calc
    HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η
        =
      twoPointMixture (c * f (1 : ℝ)) (c * f (-1 : ℝ)) := by
        simpa [twoPointMixture] using hspin
    _ =
      twoPointMixture
        (HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η ({(1 : ℝ)} : Set ℝ))
        (HopfieldOneSiteProbRatioReal.oneSiteSpinLaw (U := U) p β u η ({(-1 : ℝ)} : Set ℝ)) := by
        simp [hone, hneg]

end OneSite

end

end GibbsMeasure.Examples.HopfieldOneSiteKernelEqualityReal
