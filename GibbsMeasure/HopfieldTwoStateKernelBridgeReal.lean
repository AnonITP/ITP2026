import GibbsMeasure.HopfieldOneSiteProbRatioReal
import NeuralNetwork.NeuralNetwork.TwoState
import NeuralNetwork.NeuralNetwork.HopfieldEnergySpec
import PhysLean.Thermodynamics.Temperature.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
## One-site kernel bridge: Georgii one-site law ↔ `TwoState.gibbsUpdate` (real spins)

This file connects the SOTA `TwoState.gibbsUpdate` kernel (a `PMF` on states)
to the Georgii/DLR one-site conditional law on the spin at a fixed site `u`.

We do this by pushing `gibbsUpdate` forward along the evaluation map `s ↦ s.act u`,
yielding a `PMF ℝ` supported on `{±1}` and identifying its `+1` probability with the
same logistic parameter as the DLR computation.
-/

namespace GibbsMeasure.Examples.HopfieldTwoStateKernelBridgeReal

open MeasureTheory
open scoped ENNReal BigOperators NNReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

namespace OneSite

open TwoState
open GibbsMeasure.Examples.HopfieldOneSiteProbRatioReal

/-- The pushforward of the one-site Gibbs update `PMF` along `s' ↦ s'.act u`, as a `PMF ℝ`. -/
noncomputable def gibbsUpdateSpinPMF
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ≥0) (s : (HopfieldNetwork ℝ U).State) (u : U) : PMF ℝ :=
  PMF.map (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
    (TwoState.gibbsUpdate (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
      (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u)

lemma gibbsUpdateSpinPMF_apply_one
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ≥0) (s : (HopfieldNetwork ℝ U).State) (u : U) :
    gibbsUpdateSpinPMF (U := U) p β s u (1 : ℝ)
      =
      ENNReal.ofReal
        (TwoState.probPos (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
          (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u) := by
  classical
  -- abbreviate `pPos` and its casts as in `gibbsUpdate`
  set pPos : ℝ :=
      TwoState.probPos (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
        (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u with hpPos
  have hpPos0 : 0 ≤ pPos := by
    simpa [hpPos] using
      (TwoState.probPos_nonneg (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
        (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u)
  have hpPos1 : pPos ≤ 1 := by
    simpa [hpPos] using
      (TwoState.probPos_le_one (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
        (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u)
  let pPosNN : ℝ≥0 := ⟨pPos, hpPos0⟩
  have hpPosNN_le : pPosNN ≤ 1 := by
    change (pPosNN : ℝ) ≤ 1
    simpa using hpPos1
  -- rewrite `gibbsUpdate` with `pPosNN` and push `PMF.map` through the `bind`
  -- so we end up with a Bernoulli on `Bool` mapped to `±1`.
  have h_update :
      TwoState.gibbsUpdate (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
        (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u
        =
      PMF.bind (PMF.bernoulli pPosNN hpPosNN_le) (fun b : Bool =>
        cond b (PMF.pure (TwoState.updPos (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))
               (PMF.pure (TwoState.updNeg (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))) := by
    -- this is definitional: `gibbsUpdate` uses exactly this `bind` form
    -- after rewriting `probPos` to `pPos`.
    ext x
    simp [TwoState.gibbsUpdate, hpPos, pPosNN, hpPosNN_le, pPos]
  -- Compute the pushed-forward probability at `+1`:
  -- after pushing `PMF.map` through the `bind`, this is just the `true` mass of a Bernoulli.
  have hval :
      gibbsUpdateSpinPMF (U := U) p β s u (1 : ℝ) = (pPosNN : ℝ≥0∞) := by
    -- Push `.map` through the `bind` in the definitional presentation of `gibbsUpdate`,
    -- then evaluate at `1`. This avoids any extensionality over `ℝ`.
    have hpush :
        gibbsUpdateSpinPMF (U := U) p β s u
          =
        (PMF.bernoulli pPosNN hpPosNN_le).bind (fun b : Bool =>
          PMF.pure (cond b (1 : ℝ) (-1 : ℝ))) := by
      -- unfold and rewrite `gibbsUpdate` using `h_update`
      dsimp [gibbsUpdateSpinPMF]
      rw [h_update]
      -- push `.map` through the `bind`, then simplify the mapped `pure` branches by cases on `b`.
      -- This keeps the proof deterministic (no extensionality over `ℝ`).
      -- Start from `PMF.map_bind`:
      have hmb :
          PMF.map (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
            (PMF.bind (PMF.bernoulli pPosNN hpPosNN_le) (fun b : Bool =>
              cond b (PMF.pure (TwoState.updPos (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))
                     (PMF.pure (TwoState.updNeg (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))))
            =
            (PMF.bernoulli pPosNN hpPosNN_le).bind (fun b : Bool =>
              PMF.map (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
                (cond b (PMF.pure (TwoState.updPos (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))
                        (PMF.pure (TwoState.updNeg (NN := HopfieldNetwork ℝ U) (s := s) (u := u))))) := by
        simpa using (PMF.map_bind
          (p := PMF.bernoulli pPosNN hpPosNN_le)
          (q := fun b : Bool =>
            cond b (PMF.pure (TwoState.updPos (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))
                   (PMF.pure (TwoState.updNeg (NN := HopfieldNetwork ℝ U) (s := s) (u := u))))
          (f := fun s' : (HopfieldNetwork ℝ U).State => s'.act u))
      -- rewrite the kernel after mapping
      -- (use HopfieldEnergySpec `sPos/sNeg` to compute the `act u` value).
      -- Then conclude by congruence under `bind`.
      have hk :
          (fun b : Bool =>
              PMF.map (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
                (cond b (PMF.pure (TwoState.updPos (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))
                        (PMF.pure (TwoState.updNeg (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))))
            =
            (fun b : Bool => PMF.pure (cond b (1 : ℝ) (-1 : ℝ))) := by
        funext b
        cases b
        · -- b = false
          -- `cond false = second branch`
          -- then `map` of `pure` is `pure` of the image
          change PMF.map (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
              (PMF.pure (TwoState.updNeg (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))
            =
            PMF.pure (-1 : ℝ)
          -- switch to dot-notation to use `PMF.pure_map`
          change (PMF.pure (TwoState.updNeg (NN := HopfieldNetwork ℝ U) (s := s) (u := u))).map
              (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
            =
            PMF.pure (-1 : ℝ)
          -- reduce to the value of `act u` in the forced-negative state
          simpa [PMF.pure_map, NeuralNetwork.HopfieldEnergySpec.sNeg] using
            congrArg PMF.pure
              (NeuralNetwork.HopfieldEnergySpec.sNeg_act_self (R := ℝ) (U := U) (s := s) u)
        · -- b = true
          change PMF.map (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
              (PMF.pure (TwoState.updPos (NN := HopfieldNetwork ℝ U) (s := s) (u := u)))
            =
            PMF.pure (1 : ℝ)
          change (PMF.pure (TwoState.updPos (NN := HopfieldNetwork ℝ U) (s := s) (u := u))).map
              (fun s' : (HopfieldNetwork ℝ U).State => s'.act u)
            =
            PMF.pure (1 : ℝ)
          simpa [PMF.pure_map, NeuralNetwork.HopfieldEnergySpec.sPos] using
            congrArg PMF.pure
              (NeuralNetwork.HopfieldEnergySpec.sPos_act_self (R := ℝ) (U := U) (s := s) u)
      -- finish
      -- unfold `gibbsUpdateSpinPMF` and use `hmb`, then rewrite the kernel by `hk`.
      simpa [gibbsUpdateSpinPMF, hk] using hmb
    -- Now compute the bind at value `1`.
    -- `bind_apply` gives a `tsum` over `Bool`, and the `pure` part collapses to an `ite`.
    -- Only the `true` branch contributes.
    -- Convert the `tsum` to a `sum` over `Bool` to keep it tiny.
    rw [hpush, PMF.bind_apply]
    have h1 : (1 : ℝ) ≠ (-1 : ℝ) := by norm_num
    -- `Bool` is finite: `tsum = sum`, then the `false` branch vanishes by `h1`.
    simpa [tsum_fintype, PMF.bernoulli_apply, PMF.pure_apply, h1]
  -- Finally, identify the NNReal-coe with `ENNReal.ofReal` of the underlying real number.
  -- (`pPosNN = ⟨pPos, hpPos0⟩`.)
  -- `ENNReal.ofReal_eq_coe_nnreal` lives in `Mathlib.Data.ENNReal.Basic`.
  have hcoe : (pPosNN : ℝ≥0∞) = ENNReal.ofReal pPos := by
    -- `ENNReal.ofReal pPos` is the coercion of `⟨pPos, hpPos0⟩ : ℝ≥0`.
    simpa [pPosNN] using (ENNReal.ofReal_eq_coe_nnreal hpPos0).symm
  simpa [hval, hpPos, hcoe]

lemma gibbsUpdateSpinPMF_apply_one_toReal
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ≥0) (s : (HopfieldNetwork ℝ U).State) (u : U) :
    ENNReal.toReal (gibbsUpdateSpinPMF (U := U) p β s u (1 : ℝ))
      =
      TwoState.probPos (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
        (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u := by
  classical
  have h := gibbsUpdateSpinPMF_apply_one (U := U) (p := p) (β := β) (s := s) (u := u)
  -- `toReal (ofReal x) = x` when `0 ≤ x`.
  have hx :
      0 ≤ TwoState.probPos (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
            (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u :=
    TwoState.probPos_nonneg (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
      (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u
  simpa [h, ENNReal.toReal_ofReal hx]

end OneSite

end

end GibbsMeasure.Examples.HopfieldTwoStateKernelBridgeReal
