import GibbsMeasure.HopfieldOneSiteProbRatioReal
import GibbsMeasure.HopfieldTwoStateKernelBridgeReal
import NeuralNetwork.NeuralNetwork.HopfieldEnergySpec
import NeuralNetwork.NeuralNetwork.TwoState
import PhysLean.Thermodynamics.Temperature.Basic

/-!
## Final bridge: DLR one-site law vs `TwoState.gibbsUpdate` (real spins, Hopfield)

This file packages the “triangle closure”:

- Georgii/DLR one-site conditional probability of `σ_u = +1` (as a `Measure ℝ` on spins),
- SOTA one-site Gibbs update kernel `TwoState.gibbsUpdate` (as a `PMF` on states),

agree after pushing the `PMF` forward along `s ↦ s.act u`.

Both are identified with the same `TwoState.logisticProb (2 * β * localField)`.
-/

namespace GibbsMeasure.Examples.HopfieldOneSiteDLRvsTwoStateReal

open scoped BigOperators ENNReal NNReal

open NeuralNetwork
open TwoState

open GibbsMeasure.Examples.HopfieldOneSiteProbRatioReal
open GibbsMeasure.Examples.HopfieldTwoStateKernelBridgeReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

namespace OneSite

lemma scale_hopfield_id :
    TwoState.scale (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U) (f := (RingHom.id ℝ)) =
    (2 : ℝ) := by
  -- `scale f = f(m σ_pos) - f(m σ_neg)`, and for Hopfield: `m = id`, `σ_pos = 1`, `σ_neg = -1`.
  -- So `scale id = 1 - (-1) = 2`.
  simp [TwoState.scale, HopfieldNetwork, NeuralNetwork.instTwoStateHopfield, sub_eq_add_neg]
  norm_num

lemma probPos_hopfield_eq_logisticProb_localField
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ≥0) (s : (HopfieldNetwork ℝ U).State) (u : U) :
    TwoState.probPos (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
        (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u
      =
    TwoState.logisticProb (2 * (β : ℝ) * (NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u)) := by
  -- unfold `probPos`, rewrite `scale` and `Temperature.β (Temperature.ofβ β)`,
  -- then recognize `localField` as `net - θ`.
  classical
  unfold TwoState.probPos
  -- `κ = 2`
  have hκ :
      TwoState.scale (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U) (f := (RingHom.id ℝ)) =
      (2 : ℝ) :=
    scale_hopfield_id (U := U)
  -- `β(T.ofβ β) = β`
  have hβ : Temperature.β (Temperature.ofβ β) = β := by
    simpa using Temperature.β_ofβ β
  -- After rewriting `κ` and `β(T)`, it is a commutativity/associativity calculation inside `logisticProb`.
  -- We do it by `congrArg` + `ring_nf`.
  -- First, rewrite the argument to `logisticProb` into a simple product form.
  -- Then show it matches `2 * β * localField`.
  -- (Here `RingHom.id` and `localField = net - θ` are definitional simp.)
  have : TwoState.logisticProb
        ((2 : ℝ) *
            NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u *
            (β : ℝ))
      =
      TwoState.logisticProb (2 * (β : ℝ) * NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u) := by
    congr 1
    ring_nf
  simpa [hκ, hβ, NeuralNetwork.HopfieldEnergySpec.localField, mul_assoc, mul_left_comm, mul_comm] using this

theorem dlr_oneSite_prob_one_eq_twoState_prob_one
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ≥0) (u : U) (s : (HopfieldNetwork ℝ U).State) :
    ENNReal.toReal (oneSiteSpinLaw (U := U) p (β : ℝ) u s.act ({(1 : ℝ)} : Set ℝ))
      =
    ENNReal.toReal (OneSite.gibbsUpdateSpinPMF (U := U) p β s u (1 : ℝ)) := by
  -- DLR side: already proved as logistic in terms of `localField`.
  have h_dlr :
      ENNReal.toReal (oneSiteSpinLaw (U := U) p (β : ℝ) u s.act ({(1 : ℝ)} : Set ℝ))
        =
      TwoState.logisticProb (2 * (β : ℝ) * (NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u)) := by
    simpa using
      (oneSiteSpinLaw_apply_one_toReal_eq_logisticProb_localField (U := U) (p := p) (β := (β : ℝ))
        (u := u) (s := s))
  -- TwoState side: pushforward PMF is `probPos`, then rewrite `probPos` to the same logistic.
  have h_ts :
      ENNReal.toReal (OneSite.gibbsUpdateSpinPMF (U := U) p β s u (1 : ℝ))
        =
      TwoState.probPos (R := ℝ) (U := U) (σ := ℝ) (NN := HopfieldNetwork ℝ U)
        (f := (RingHom.id ℝ)) p (Temperature.ofβ β) s u := by
    simpa using
      (GibbsMeasure.Examples.HopfieldTwoStateKernelBridgeReal.OneSite.gibbsUpdateSpinPMF_apply_one_toReal
        (U := U) (p := p) (β := β) (s := s) (u := u))
  have h_ts' :
      ENNReal.toReal (OneSite.gibbsUpdateSpinPMF (U := U) p β s u (1 : ℝ))
        =
      TwoState.logisticProb (2 * (β : ℝ) * (NeuralNetwork.HopfieldEnergySpec.localField (R := ℝ) (U := U) p s u)) := by
    simpa [probPos_hopfield_eq_logisticProb_localField (U := U) (p := p) (β := β) (s := s) (u := u)] using h_ts
  -- conclude
  exact h_dlr.trans h_ts'.symm

end OneSite

end

end GibbsMeasure.Examples.HopfieldOneSiteDLRvsTwoStateReal
