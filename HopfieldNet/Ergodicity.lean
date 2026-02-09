import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Stochastic
import MCMC.Finite.Core
import MCMC.Finite.toKernel
import HopfieldNet.DetailedBalanceBM

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.openClassical false

/-!
# Ergodicity of the Random–Scan Gibbs Kernel via Perron–Frobenius

This module provides the Perron–Frobenius (PF) route to ergodicity for the
random–scan single–site Gibbs sampler associated with a finite two–state
Hopfield–style neural network endowed with an `EnergySpec'`.

The goal is to bridge:
1. The constructive, site–local stochastic dynamics (`randomScanKernel`) built
   earlier from single–site Gibbs updates (`singleSiteKernel`), and
2. The global spectral framework for non–negative matrices developed in
   `Mathematics/LinearAlgebra/Matrix/PerronFrobenius/*`.

Together these prove that the Markov chain
is:
- aperiodic (positive diagonal),
- irreducible (every state communicates with every other),
- and possesses a unique stationary law in the probability simplex
  (the Perron eigenvector of the column–stochastic transition matrix).

## Position in the Framework

This file sits at the interface of:
- `TwoState.lean`: abstract two–state neural networks and their Gibbs kernels.
- `DetailedBalanceBM.lean`: detailed balance / reversibility (microscopic symmetry).
- `toCanonicalEnsemble.lean`: embedding into the canonical ensemble formalism.
- `Mathematics/.../PerronFrobenius/`: general matrix PF technology (paths, irreducibility,
  primitive matrices, uniqueness of positive eigenvectors, stochastic normalization).

While detailed balance already implies invariance of the Boltzmann distribution,
the PF approach supplies an *independent* global argument for uniqueness and
ergodicity that scales conceptually to potential future relaxations (e.g.
non‑reversible perturbations, comparison arguments, or multi–ensemble couplings).

## Core Constructions

* `RScol`: the column–stochastic real matrix extracted from the random–scan kernel
  (column `t` lists transition probabilities from state `t` to all targets `s`).
  We pass to `ℝ` via `ENNReal.toReal` after verifying finiteness.

* `diffSites`, `DiffOnly`: combinatorial bookkeeping of Hamming differences
  between network states.

* Local reduction lemma:
  - `exists_single_flip_reduce`: constructs a one–site flip that strictly
    decreases the number of differing coordinates with respect to a target.

With these, we construct an induction that produces a strictly
positive entry in some power `(RScol)^n` between any ordered pair of states,
proving the irreducibility of `RScol` (as a non–negative matrix).

## Main Results

* `RScol_nonneg`: entrywise non–negativity.
* `RScol_colsum_one`: stochastic (column sums = 1).
* `RScol_diag_pos`: aperiodicity (strictly positive self–loops).
* `RScol_exists_positive_power`: combinatorial lemma.
* `RScol_irreducible`: strong connectivity ⇒ matrix irreducible in PF sense.
* `RScol_unique_stationary_simplex`: Perron–Frobenius uniqueness of the
  stationary vector in the simplex.
* `randomScan_ergodic_and_uniqueInvariant`:
  package theorem: reversibility, aperiodicity, irreducibility, uniqueness.

## Methodological Notes

1. We separate:
   - Local algebraic / probabilistic identities (logistic update probabilities).
   - Set–theoretic combinatorics on spin configurations.
   - Matrix / quiver path reasoning abstracted in the `PerronFrobenius` namespace.

2. Irreducibility proof strategy:
   - Measure the Hamming distance (# differing sites).
   - Show existence of a transition that decreases it by one.
   - Conclude positivity of a path product ⇒ positive matrix power entry.

3. Aperiodicity does not rely on global structure: the single–site kernel
   retains the current state with strictly positive probability at any temperature.

4. The Perron vector produced here is *not* explicitly identified with the
   Boltzmann distribution in this file (that is done via detailed balance),
   but uniqueness ensures both coincide.

## Design Choices

* Column–stochastic orientation (as opposed to row–stochastic) matches our
  kernel evaluation convention `(κ t {s})`.
* Irreducibility is phrased through the quiver induced by positive entries:
  we reuse path existence lemmas from the PF layer.

## Extensibility

Future directions facilitated by this layout:
- Spectral gap estimates (via comparison theorems or Dirichlet forms).
- Low–temperature metastability analysis (using structure of RScol powers).
- Non–reversible accelerations (lifting beyond detailed balance while still
  invoking PF arguments on modified operators).
- Multi–spin block updates (replace single–site combinatorics with block geometry).

## References

* E.Seneta, 'Non-negative Matrices and Markov Chains'

## Notational Conventions

* `κ` (kappa): random–scan kernel.
* `RScol`: real matrix of κ (column–stochastic).
* `β = T.β`: inverse temperature.
* Set difference tracking via `diffSites`.

-/
section Ergodicity

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped ENNReal
open TwoState HopfieldBoltzmann ProbabilityTheory Matrix
open MeasureTheory

variable {U σ : Type} [Fintype U] [DecidableEq U] [Nonempty U]
variable (NN : NeuralNetwork ℝ U σ)
variable [Fintype NN.State] [DecidableEq NN.State] [Nonempty NN.State]
variable [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
variable (spec : TwoState.EnergySpec' (NN:=NN))
variable (p : Params NN) (T : Temperature)

local notation "κ" => randomScanKernel (NN:=NN) spec p T

/-- Column-stochastic transition matrix for the random-scan kernel.
Column `t` sums to 1: entries are (probability to go from `t` to `s`). -/
noncomputable def RScol (NN : NeuralNetwork ℝ U σ)
    [Fintype NN.State] [DecidableEq NN.State] [Nonempty NN.State]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature) :
    Matrix NN.State NN.State ℝ :=
  fun s t => ((randomScanKernel (NN:=NN) spec p T) t {s}).toReal

lemma RScol_nonneg :
  ∀ s t, 0 ≤ RScol (NN:=NN) (spec:=spec) p T s t := by
  intro s t; dsimp [RScol]; exact ENNReal.toReal_nonneg

/-- Column sums are 1 (column-stochastic). -/
lemma RScol_colsum_one :
  ∀ t, (∑ s, RScol (NN:=NN) (spec:=spec) p T s t) = 1 := by
  intro t
  -- make all sets measurable (finite discrete space)
  letI : MeasurableSpace NN.State := ⊤
  letI : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩
  -- Fix the PMF that generates the measure (κ t ·)
  set q :
      PMF NN.State :=
    (PMF.uniformOfFintype U).bind
      (fun u => TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T t u) with hq
  -- Evaluate the kernel at t as the measure induced by q
  have hκ_eval : ∀ B, (κ t) B = q.toMeasure B := by
    intro B
    simp [randomScanKernel, pmfToKernel, Kernel.ofFunOfCountable, hq]
    aesop
  have h1 :
    (∑ s, (κ t {s})) = (κ t Set.univ) := by
    -- Use q.toMeasure on both sides
    have h_singleton : ∀ s : NN.State, q.toMeasure {s} = q s := by
      intro s
      simpa using (PMF.toMeasure_singleton (p:=q) s)
    have hsum_q : ∑ s, q s = (1 : ℝ≥0∞) := by
      simpa [tsum_fintype] using q.tsum_coe
    have h1' :
        (∑ s, q.toMeasure {s}) = (q.toMeasure (Set.univ : Set NN.State)) := by
      calc
        (∑ s, q.toMeasure {s})
            = ∑ s, q s := by
              refine Finset.sum_congr rfl ?_
              intro s _
              simpa using (h_singleton s)
        _ = (1 : ℝ≥0∞) := hsum_q
        _ = q.toMeasure Set.univ := by simp
    -- now replace κ with q.toMeasure on both sides
    simpa [hκ_eval] using h1'
  -- Probability measure on univ
  have hK_univ : (κ t Set.univ) = 1 := by
    -- q.toMeasure univ = 1
    calc
      κ t Set.univ = q.toMeasure Set.univ := by simp [hκ_eval]
      _ = (1 : ℝ≥0∞) := by simp
  -- Each singleton has finite mass (< ⊤)
  have hfin : ∀ s, (κ t {s}) ≠ ∞ := by
    intro s
    have hle' : (κ t {s}) ≤ (κ t Set.univ) := by
      -- monotonicity of measure: {s} ⊆ univ
      have hsub : ({s} : Set NN.State) ⊆ Set.univ := by intro _ _; trivial
      simpa using (measure_mono hsub : (κ t {s}) ≤ (κ t Set.univ))
    have hle : (κ t {s}) ≤ (1 : ℝ≥0∞) := by simpa [hK_univ] using hle'
    exact ne_of_lt (lt_of_le_of_lt hle (by simp))
  -- Move toReal inside the finite sum
  have hsum_toReal :
    (∑ s, (κ t {s}).toReal)
      = ((∑ s, (κ t {s}))).toReal := by
    have h :=
      ENNReal.toReal_sum
        (s := (Finset.univ : Finset NN.State))
        (f := fun s => (κ t {s}))
        (by intro s _; exact hfin s)
    simpa using h.symm
  calc
    (∑ s, RScol (NN:=NN) (spec:=spec) p T s t)
        = (∑ s, (κ t {s}).toReal) := by
            rfl
    _ = ((∑ s, (κ t {s}))).toReal := hsum_toReal
    _ = ((κ t Set.univ)).toReal := by simp [h1]
    _ = (1 : ℝ) := by simp [hK_univ]

/-- Positive diagonal: the random-scan kernel has K(s→s) > 0 (aperiodicity). -/
lemma RScol_diag_pos :
  ∀ s, 0 < RScol (NN:=NN) (spec:=spec) p T s s := by
  intro s
  -- random-scan as uniform average of single-site kernels on {s}
  have hκ :
    κ s {s}
      =
    (∑ u : U, (singleSiteKernel (NN:=NN) spec p T u) s {s}) / (Fintype.card U : ℝ≥0∞) := by
    have := randomScanKernel_eval_uniform (NN:=NN) (spec:=spec) (p:=p) (T:=T) s {s} (by trivial)
    simpa using this
  -- Each single-site update stays put with strictly positive probability:
  have h_u_pos : ∀ u : U,
      0 < (singleSiteKernel (NN:=NN) spec p T u) s {s} := by
    intro u
    -- Reduce to positivity of the real kernel
    have h_eval :
        (singleSiteKernel (NN:=NN) spec p T u) s {s}
          = ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN:=NN) p T u s s) := by
      simpa using
        singleSiteKernel_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) u s s
    have hstay_real :
        0 < HopfieldBoltzmann.Kbm (NN:=NN) p T u s s := by
      -- classify at site u
      rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u) with hpos | hneg
      · -- s = updPos s u, so Kbm equals probPos > 0
        have hfix : s = updPos (NN:=NN) s u := by
          ext v; by_cases hv : v = u
          · subst hv; simp [updPos_act_at_u, hpos]
          · simp [updPos_act_noteq (NN:=NN) s u v hv]
        have hK := Kbm_apply_updPos (NN:=NN) (p:=p) (T:=T) u s
        have hK_eq :
            HopfieldBoltzmann.Kbm (NN:=NN) p T u s s
              = probPos (NN:=NN) (RingHom.id ℝ) p T s u := by
          dsimp [hfix]; grind
        have hprob : 0 < probPos (NN:=NN) (RingHom.id ℝ) p T s u := by
          unfold TwoState.probPos; exact logisticProb_pos' _
        simpa [hK_eq] using hprob
      · -- s = updNeg s u, so Kbm equals 1 - probPos > 0
        have hfix : s = updNeg (NN:=NN) s u := by
          ext v; by_cases hv : v = u
          · subst hv; simp [updNeg_act_at_u, hneg]
          · simp [updNeg_act_noteq (NN:=NN) s u v hv]
        have hK := Kbm_apply_updNeg (NN:=NN) (p:=p) (T:=T) u s
        have hK_eq :
            HopfieldBoltzmann.Kbm (NN:=NN) p T u s s
              = 1 - probPos (NN:=NN) (RingHom.id ℝ) p T s u := by
          rw [hfix]; grind
        have hprobc : 0 < 1 - probPos (NN:=NN) (RingHom.id ℝ) p T s u := by
          unfold TwoState.probPos; exact one_sub_logistic_pos _
        simpa [hK_eq] using hprobc
    -- back to ENNReal via ofReal_pos
    have h_ofReal_pos : 0 < ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN:=NN) p T u s s) :=
      ENNReal.ofReal_pos.mpr hstay_real
    simpa [h_eval] using h_ofReal_pos
  -- Sum over sites is positive: we pick any site u0 and bound from below by its positive contribution
  have hsum_pos :
    0 < (∑ u : U, (singleSiteKernel (NN:=NN) spec p T u) s {s}) := by
    obtain ⟨u0⟩ := ‹Nonempty U›
    have hnonneg : ∀ u : U, 0 ≤ (singleSiteKernel (NN:=NN) spec p T u) s {s} := by
      intro u; exact le_of_lt (h_u_pos u)
    have hle :
      (singleSiteKernel (NN:=NN) spec p T u0) s {s}
        ≤ ∑ u : U, (singleSiteKernel (NN:=NN) spec p T u) s {s} := by
      have hnonneg' : ∀ u ∈ (Finset.univ : Finset U),
          0 ≤ (singleSiteKernel (NN:=NN) spec p T u) s {s} := by
        intro u _; exact hnonneg u
      exact Finset.single_le_sum hnonneg' (by simp)
    exact lt_of_lt_of_le (h_u_pos u0) hle
  -- Denominator is positive and finite
  have hcard_pos : 0 < (Fintype.card U : ℝ≥0∞) := by
    exact_mod_cast (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance))
  have hden_ne : (Fintype.card U : ℝ≥0∞) ≠ 0 := by exact ne_of_gt hcard_pos
  -- The average is positive in ℝ≥0∞
  have hdiv_pos :
    0 < (∑ u : U, (singleSiteKernel (NN:=NN) spec p T u) s {s}) / (Fintype.card U : ℝ≥0∞) := by
    exact ENNReal.div_pos_iff.mpr ⟨ne_of_gt hsum_pos, by simp⟩
  -- Move to ℝ via toReal: also show finiteness by bounding with 1
  have h_toReal_pos : 0 < (κ s {s}).toReal := by
    -- show: ((∑ ...)/card) ≤ 1, hence ≠ ∞
    have hle_one_avg :
      (∑ u : U, (singleSiteKernel (NN:=NN) spec p T u) s {s}) / (Fintype.card U : ℝ≥0∞) ≤ 1 := by
      -- κ s {s} ≤ κ s univ = 1, and rewrite κ by hκ
      letI : MeasurableSpace NN.State := ⊤
      letI : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩
      have hsub : ({s} : Set NN.State) ⊆ Set.univ := by intro _ _; trivial
      have hmono : κ s {s} ≤ κ s Set.univ := by
        simpa using (measure_mono hsub : (κ s {s}) ≤ (κ s Set.univ))
      -- κ s Set.univ = 1
      have h_univ : κ s Set.univ = 1 := by
        have hunif :=
          randomScanKernel_eval_uniform (NN:=NN) (spec:=spec) (p:=p) (T:=T) s Set.univ (by trivial)
        have h_one : ∀ u : U, (singleSiteKernel (NN:=NN) spec p T u) s Set.univ = 1 := by
          intro u; unfold singleSiteKernel pmfToKernel; simp
        -- average of ones is one
        have hcard_ne_zero : (Fintype.card U : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast (Fintype.card_ne_zero : Fintype.card U ≠ 0)
        have hfinite : (Fintype.card U : ℝ≥0∞) ≠ ∞ := by simp
        -- average of ones over U is (card U) / (card U) = 1 in ℝ≥0∞
        simpa [h_one, Finset.card_univ, Finset.sum_const, ENNReal.div_self, hcard_ne_zero, hfinite] using hunif
      have : κ s {s} ≤ 1 := by simpa [h_univ] using hmono
      simpa [hκ] using this
    -- Convert ≤ 1 into < ⊤ to use toReal_pos_iff
    have hlt_top :
      (∑ u : U, (singleSiteKernel (NN:=NN) spec p T u) s {s}) / (Fintype.card U : ℝ≥0∞) < ⊤ := by
      exact lt_of_le_of_lt hle_one_avg (by simp)
    simpa [hκ] using ENNReal.toReal_pos_iff.mpr ⟨hdiv_pos, hlt_top⟩
  -- RScol definition
  simpa [RScol] using h_toReal_pos

/-- States that differ only at `u`. -/
def DiffOnly (u : U) (s s' : NN.State) : Prop :=
  (∀ v ≠ u, s.act v = s'.act v) ∧ s.act u ≠ s'.act u

lemma RScol_pos_of_diffOnly
  {u : U} {s s' : NN.State}
  (h : DiffOnly (NN:=NN) u s s') :
  0 < RScol (NN:=NN) (spec:=spec) p T s s' := by
  -- random-scan as uniform average of single-site kernels
  have hκ :
    κ s' {s}
      =
    (∑ v : U, (singleSiteKernel (NN:=NN) spec p T v) s' {s}) / (Fintype.card U : ℝ≥0∞) := by
    have := randomScanKernel_eval_uniform (NN:=NN) (spec:=spec) (p:=p) (T:=T) s' {s} (by trivial)
    simpa using this
  -- all sites ≠ u contribute 0 by `Kbm_zero_of_diffAway`
  have hzero :
      ∀ v ≠ u, (singleSiteKernel (NN:=NN) spec p T v) s' {s} = 0 := by
    intro v hv
    have hdiffAway :
      DiffAway (NN:=NN) v s' s := by
      rcases h with ⟨hoff, hneq⟩
      refine ⟨u, ?_, ?_⟩
      · simpa [ne_comm] using hv
      · simpa using hneq.symm
    have hz := Kbm_zero_of_diffAway (NN:=NN) (p:=p) (T:=T) (u:=v) (s:=s') (s':=s) hdiffAway
    have h_eval :
        (singleSiteKernel (NN:=NN) spec p T v) s' {s}
        = ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN:=NN) p T v s' s) := by
      simpa using
        singleSiteKernel_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) v s' s
    simp [h_eval, hz.1]
  -- site u contributes strictly positive mass (flip towards s)
  have hpos_u :
      0 < (singleSiteKernel (NN:=NN) spec p T u) s' {s} := by
    -- classify at site u
    have h_off' : ∀ v ≠ u, s'.act v = s.act v := by
      intro v hv; rcases h with ⟨hoff, _⟩; simpa using (hoff v hv).symm
    -- difference at u
    have hneq : s.act u ≠ s'.act u := h.2
    -- case on s'.act u
    rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s'.act u)).1 (s'.hp u) with hpos' | hneg'
    · -- s'.act u = σ_pos, hence s.act u = σ_neg
      have hs_neg :
          s.act u = TwoStateNeuralNetwork.σ_neg (NN:=NN) := by
        rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u) with hspos | hsneg
        · exact (False.elim (hneq (by simpa [hpos'] using hspos)))
        · exact hsneg
      -- s = updNeg s' u
      have hfix : s = updNeg (NN:=NN) s' u := by
        ext v
        by_cases hv : v = u
        · subst hv; simp [updNeg_act_at_u, hs_neg]
        · have := h_off' v hv
          simp [updNeg_act_noteq (NN:=NN) s' u v hv, this]
      -- express Kbm and show positivity
      have hK := Kbm_apply_updNeg (NN:=NN) (p:=p) (T:=T) u s'
      have hK_eq :
          HopfieldBoltzmann.Kbm (NN:=NN) p T u s' s
            = 1 - probPos (NN:=NN) (RingHom.id ℝ) p T s' u := by
        simpa [hfix] using hK
      have hprobc : 0 < 1 - probPos (NN:=NN) (RingHom.id ℝ) p T s' u := by
        unfold TwoState.probPos; exact one_sub_logistic_pos _
      have hreal_pos : 0 < HopfieldBoltzmann.Kbm (NN:=NN) p T u s' s := by
        simpa [hK_eq] using hprobc
      -- back to ENNReal
      have h_eval :=
        singleSiteKernel_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) u s' s
      have : 0 < ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN:=NN) p T u s' s) :=
        ENNReal.ofReal_pos.mpr hreal_pos
      simpa [h_eval] using this
    · -- s'.act u = σ_neg, hence s.act u = σ_pos
      have hs_pos :
          s.act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) := by
        rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s.act u)).1 (s.hp u) with hspos | hsneg
        · exact hspos
        · exact (False.elim (hneq (by simpa [hneg'] using hsneg)))
      -- s = updPos s' u
      have hfix : s = updPos (NN:=NN) s' u := by
        ext v
        by_cases hv : v = u
        · subst hv; simp [updPos_act_at_u, hs_pos]
        · have := h_off' v hv
          simp [updPos_act_noteq (NN:=NN) s' u v hv, this]
      -- express Kbm and show positivity
      have hK := Kbm_apply_updPos (NN:=NN) (p:=p) (T:=T) u s'
      have hK_eq :
          HopfieldBoltzmann.Kbm (NN:=NN) p T u s' s
            = probPos (NN:=NN) (RingHom.id ℝ) p T s' u := by
        simpa [hfix] using hK
      have hprobc : 0 < probPos (NN:=NN) (RingHom.id ℝ) p T s' u := by
        unfold TwoState.probPos; exact logisticProb_pos' _
      have hreal_pos : 0 < HopfieldBoltzmann.Kbm (NN:=NN) p T u s' s := by
        simpa [hK_eq] using hprobc
      have h_eval :=
        singleSiteKernel_singleton_eval (NN:=NN) (spec:=spec) (p:=p) (T:=T) u s' s
      have : 0 < ENNReal.ofReal (HopfieldBoltzmann.Kbm (NN:=NN) p T u s' s) :=
        ENNReal.ofReal_pos.mpr hreal_pos
      simpa [h_eval] using this
  -- sum reduces to the u-term and is > 0, so the average is > 0
  have hsum :
      (∑ v : U, (singleSiteKernel (NN:=NN) spec p T v) s' {s})
        = (singleSiteKernel (NN:=NN) spec p T u) s' {s} := by
    classical
    refine
      (Finset.sum_eq_single u
        (fun v hv hne => by simp [hzero v hne])
        (by simp)).trans ?_
    simp
  have hcol_pos :
      0 < (κ s' {s}).toReal := by
    -- positivity in ℝ≥0∞
    have hdiv_pos :
      0 < ((singleSiteKernel (NN:=NN) spec p T u) s' {s}) / (Fintype.card U : ℝ≥0∞) := by
      exact ENNReal.div_pos_iff.mpr ⟨ne_of_gt hpos_u, by simp⟩
    have hκ_pos : 0 < κ s' {s} := by
      simpa [hκ, hsum] using hdiv_pos
    -- bound by 1 to ensure finiteness
    letI : MeasurableSpace NN.State := ⊤
    letI : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩
    have hunif :=
      randomScanKernel_eval_uniform (NN:=NN) (spec:=spec) (p:=p) (T:=T) s' Set.univ (by trivial)
    have h_one : ∀ v : U, (singleSiteKernel (NN:=NN) spec p T v) s' Set.univ = 1 := by
      intro v; unfold singleSiteKernel pmfToKernel; simp
    have hcard_ne_zero : (Fintype.card U : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card U ≠ 0)
    have hfinite : (Fintype.card U : ℝ≥0∞) ≠ ∞ := by simp
    have h_univ :
        κ s' Set.univ = 1 := by
      simpa [h_one, Finset.card_univ, Finset.sum_const,
             ENNReal.div_self, hcard_ne_zero, hfinite] using hunif
    have h_le_one : κ s' {s} ≤ 1 := by
      have hsub : ({s} : Set NN.State) ⊆ Set.univ := by intro _ _; trivial
      have hmono : κ s' {s} ≤ κ s' Set.univ := by
        simpa using (measure_mono hsub : (κ s' {s}) ≤ (κ s' Set.univ))
      simpa [h_univ] using hmono
    have h_lt_top : κ s' {s} < ⊤ := lt_of_le_of_lt h_le_one (by simp)
    have : 0 < (κ s' {s}).toReal :=
      (ENNReal.toReal_pos_iff).mpr ⟨hκ_pos, h_lt_top⟩
    exact this
  simpa [RScol] using hcol_pos

open Classical

/-- Sites (as a Finset) where two states differ. -/
noncomputable def diffSites
    (NN : NeuralNetwork ℝ U σ) [Fintype U] [DecidableEq U]
    (s s' : NN.State) : Finset U :=
  (Finset.univ.filter (fun u : U => s.act u ≠ s'.act u))

lemma diffSites_card_zero
    (NN : NeuralNetwork ℝ U σ) [Fintype U] [DecidableEq U]
    {s s' : NN.State} :
    (diffSites (NN:=NN) s s').card = 0 → s = s' := by
  intro h0
  ext u
  have : u ∈ (Finset.univ.filter fun v : U => s.act v ≠ s'.act v) → False := by
    intro hu
    have hpos : 0 < (diffSites (NN:=NN) s s').card :=
      Finset.card_pos.mpr ⟨u, hu⟩
    simp [h0] at hpos
  by_contra hneq
  have : u ∈ diffSites (NN:=NN) s s' := by
    simp [diffSites, hneq]
  simp_all only [Finset.card_eq_zero, ne_eq, Finset.mem_filter, Finset.mem_univ, not_false_eq_true, and_self,
    imp_false, not_true_eq_false]

/-- One-step “towards-target” flip: picking a differing site reduces the number of differences.
Given a site `u` where `s` and `s'` differ, build a state `s₁` that differs from `s` only at `u`
(by setting that coordinate equal to `s'.act u`), so that the number of differing sites to `s'`
drops by exactly one. -/
lemma exists_single_flip_reduce
    (NN : NeuralNetwork ℝ U σ) [Fintype U] [DecidableEq U]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature)
    {s s' : NN.State} {u : U}
    (hu : u ∈ diffSites (NN:=NN) s s') :
    ∃ s₁ : NN.State,
      DiffOnly (NN:=NN) u s₁ s ∧
      (diffSites (NN:=NN) s₁ s').card + 1 = (diffSites (NN:=NN) s s').card := by
  -- The site really differs
  have hneq : s.act u ≠ s'.act u := by
    simp [diffSites] at hu; exact hu
  -- Classify `s'.act u` (two-state exclusive)
  rcases (TwoStateExclusive.pact_iff (NN:=NN) (a:=s'.act u)).1 (s'.hp u) with hpos | hneg
  · -- Target value is σ_pos: use updPos
    refine ⟨updPos (NN:=NN) s u, ?_, ?_⟩
    -- (1) DiffOnly property
    · refine And.intro ?hcoord ?hdiffu
      · intro v hv
        -- Off-site unchanged
        simp [updPos, Function.update, hv]
      · -- At u it flips
        have hup : (updPos (NN:=NN) s u).act u = TwoStateNeuralNetwork.σ_pos (NN:=NN) := by
          simp [updPos]
        -- Need (updPos s u).act u ≠ s.act u
        intro hcontra
        -- Then s.act u = σ_pos = s'.act u contradicting hneq
        have : s.act u = s'.act u := by
          simpa [hpos, hup] using hcontra.symm
        exact hneq this
    -- (2) Cardinal reduction
    · -- Show diffSites after update is erase u
      have hset :
          diffSites (NN:=NN) (updPos (NN:=NN) s u) s'
            = (diffSites (NN:=NN) s s').erase u := by
        ext v
        by_cases hvu : v = u
        · subst hvu
          -- v = u: new state matches s' at u, so not in diffSites; RHS also erased
          simp [diffSites, updPos, Function.update, hpos]
        · -- v ≠ u: predicate unaffected
          simp [diffSites, updPos, Function.update, hvu]
      have hmem : u ∈ diffSites (NN:=NN) s s' := hu
      have hcount :
          (diffSites (NN:=NN) (updPos (NN:=NN) s u) s').card
            = (diffSites (NN:=NN) s s').card - 1 := by
        simpa [hset] using Finset.card_erase_of_mem hmem
      -- Convert to +1 form
      have hposCard :
          0 < (diffSites (NN:=NN) s s').card :=
        Finset.card_pos.mpr ⟨u, hu⟩
      have hge : 1 ≤ (diffSites (NN:=NN) s s').card :=
        Nat.succ_le_of_lt hposCard
      have :
          (diffSites (NN:=NN) (updPos (NN:=NN) s u) s').card + 1
            = (diffSites (NN:=NN) s s').card := by
        have := Nat.sub_add_cancel hge
        simpa [hcount] using this
      simp [this]
  · -- Target value is σ_neg: use updNeg (s'.act u = σ_neg)
    refine ⟨updNeg (NN:=NN) s u, ?_, ?_⟩
    -- (1) DiffOnly property
    · refine And.intro
        (by
          intro v hv
          simp [updNeg, Function.update, hv]
        )
        (by
          have hup : (updNeg (NN:=NN) s u).act u = TwoStateNeuralNetwork.σ_neg (NN:=NN) := by
            simp [updNeg]
          intro hcontra
          have : s.act u = s'.act u := by
            simpa [hneg, hup] using hcontra.symm
          exact hneq this
        )
    -- (2) Cardinal reduction
    · have hset :
          diffSites (NN:=NN) (updNeg (NN:=NN) s u) s'
            = (diffSites (NN:=NN) s s').erase u := by
        ext v
        by_cases hvu : v = u
        · subst hvu
          simp [diffSites, updNeg, Function.update, hneg]
        · simp [diffSites, updNeg, Function.update, hvu]
      have hmem : u ∈ diffSites (NN:=NN) s s' := hu
      have hcount :
          (diffSites (NN:=NN) (updNeg (NN:=NN) s u) s').card
            = (diffSites (NN:=NN) s s').card - 1 := by
        simpa [hset] using Finset.card_erase_of_mem hmem
      have hposCard :
          0 < (diffSites (NN:=NN) s s').card :=
        Finset.card_pos.mpr ⟨u, hu⟩
      have hge : 1 ≤ (diffSites (NN:=NN) s s').card :=
        Nat.succ_le_of_lt hposCard
      have :
          (diffSites (NN:=NN) (updNeg (NN:=NN) s u) s').card + 1
            = (diffSites (NN:=NN) s s').card := by
        have := Nat.sub_add_cancel hge
        simpa [hcount] using this
      simp [this]

/-- Nonnegativity of all powers of `RScol`. -/
lemma RScol_pow_nonneg
    (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature) :
    ∀ n (i j : NN.State), 0 ≤ (RScol (NN:=NN) (spec:=spec) p T ^ n) i j := by
  intro n; induction' n with n ih <;> intro i j
  · -- base case n = 0
    by_cases h : i = j
    · subst h; simp [pow_zero]
    · simp [pow_zero, h]
  · -- inductive step
    have hmul :
        (RScol (NN:=NN) (spec:=spec) p T ^ (Nat.succ n)) i j
          = ∑ k, (RScol (NN:=NN) (spec:=spec) p T ^ n) i k *
                  RScol (NN:=NN) (spec:=spec) p T k j := by
      simp [pow_succ, Matrix.mul_apply]
    have hterm :
        ∀ k, 0 ≤ (RScol (NN:=NN) (spec:=spec) p T ^ n) i k *
               RScol (NN:=NN) (spec:=spec) p T k j := by
      intro k
      have h1 := ih i k
      have h2 := RScol_nonneg (NN:=NN) (spec:=spec) (p:=p) (T:=T) k j
      exact mul_nonneg h1 h2
    have hsum : 0 ≤ ∑ k, (RScol (NN:=NN) (spec:=spec) p T ^ n) i k *
                          RScol (NN:=NN) (spec:=spec) p T k j :=
      Finset.sum_nonneg (fun k _ => hterm k)
    simpa [hmul]

/-- Existence of a positive entry in some power between any two states. -/
lemma RScol_exists_positive_power
    (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature)
    (s s' : NN.State) :
    ∃ n : ℕ, 0 < (RScol (NN:=NN) (spec:=spec) p T ^ n) s' s := by
  set A := RScol (NN:=NN) (spec:=spec) p T
  -- Auxiliary: recursion on number of differing sites.
  have hPow := RScol_pow_nonneg (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  have main :
      ∀ k, ∀ s s' : NN.State,
        (diffSites (NN:=NN) s s').card = k →
        ∃ n, 0 < (A ^ n) s' s := by
    refine Nat.rec ?base ?step
    · -- k = 0 : states equal ⇒ take n=0
      intro s s' hcard
      have hs_eq : s = s' :=
        diffSites_card_zero (NN:=NN) (s:=s) (s':=s') hcard
      subst hs_eq
      refine ⟨0, ?_⟩
      simp [A]              -- (A^0) diagonal entry = 1
    · -- k.succ
      intro k IH s s' hcard
      -- There is at least one differing site
      have hpos : 0 < (diffSites (NN:=NN) s s').card := by
        simp_rw [hcard]
        grind
      obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      -- One-step flip towards s'
      obtain ⟨s₁, hDiffOnly, hreduce⟩ :=
        exists_single_flip_reduce (NN:=NN) (spec:=spec) (p:=p) (T:=T) hu
      -- From (|diffSites s₁ s'| + 1 = |diffSites s s'| = k+1)
      have hcard_s₁ :
          (diffSites (NN:=NN) s₁ s').card = k := by
        -- hreduce : (diffSites s₁ s').card + 1 = (diffSites s s').card
        -- rewrite RHS via hcard
        have h1 :
            (diffSites (NN:=NN) s₁ s').card + 1 = Nat.succ k := by
          simpa [hcard] using hreduce
        exact Nat.succ.inj h1
      -- One-step positivity (A s₁ s > 0)
      have h_step :
          0 < A s₁ s := by
        simpa [A] using
          RScol_pos_of_diffOnly (NN:=NN) (spec:=spec) (p:=p) (T:=T) hDiffOnly
      -- Inductive hypothesis on k for s₁ → s'
      obtain ⟨n, hn_pos⟩ := IH s₁ s' hcard_s₁
      -- Combine: positive path length n from s'→s₁ then one more step s₁→s
      refine ⟨n.succ, ?_⟩
      have hsum :
          (A ^ (Nat.succ n)) s' s
            = ∑ j, (A ^ n) s' j * A j s := by
        simp only [Nat.succ_eq_add_one]
        exact rfl
      -- Chosen strictly positive summand j = s₁
      have hchosen :
          0 < (A ^ n) s' s₁ * A s₁ s := mul_pos hn_pos h_step
      -- Nonnegativity of all summands
      have hterm_nonneg :
          ∀ j, 0 ≤ (A ^ n) s' j * A j s := by
        intro j
        have h1 := hPow n s' j
        have h2 := RScol_nonneg (NN:=NN) (spec:=spec) (p:=p) (T:=T) j s
        exact mul_nonneg h1 h2
      -- Sum ≥ chosen term ⇒ strictly positive
      have hge :
          (A ^ n) s' s₁ * A s₁ s
            ≤ ∑ j, (A ^ n) s' j * A j s := by
        have hnonneg :
          ∀ j ∈ (Finset.univ : Finset NN.State),
            0 ≤ (A ^ n) s' j * A j s := by
          intro j hj; exact hterm_nonneg j
        have hmem : s₁ ∈ (Finset.univ : Finset NN.State) := by simp
        exact Finset.single_le_sum hnonneg hmem
      have hsum_pos :
          0 < ∑ j, (A ^ n) s' j * A j s :=
        lt_of_lt_of_le hchosen hge
      simpa [hsum] using hsum_pos
  -- Apply recursion with k = |diffSites s s'|
  exact main (diffSites (NN:=NN) s s').card s s' rfl

/-- Irreducible: positive path between any two states. -/
lemma RScol_irred
    (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature) :
    Matrix.IsIrreducible (RScol (NN:=NN) (spec:=spec) p T) := by
  -- Set A := transition matrix
  set A := RScol (NN:=NN) (spec:=spec) p T
  -- Provide the graph structure induced by A for subsequent Path constructions.
  letI : Quiver NN.State := Matrix.toQuiver A
  -- Non‑negativity part
  refine ⟨(RScol_nonneg (NN:=NN) (spec:=spec) (p:=p) (T:=T)), ?_⟩
  -- Strong connectivity: for any s s', produce a positive–length path s ⟶ s'
  intro s s'
  -- We have a positive entry in some power (possibly n = 0)
  obtain ⟨n, hpos⟩ :=
    RScol_exists_positive_power (NN:=NN) (spec:=spec) (p:=p) (T:=T) s' s
    -- note: order (s', s) chosen so that hpos : 0 < (A^n) s s'
  -- If n = 0 we only know a diagonal entry of A^0 is positive, forcing s = s'
  by_cases hzero : n = 0
  · subst hzero
    -- From positivity of (A^0) s s' infer s = s'
    have hs_eq : s = s' := by
      -- A^0 = 1, so the (s,s') entry is (if s = s' then 1 else 0)
      have h := hpos
      simp [pow_zero] at h
      by_contra hne
      simp [hne] at h
    subst hs_eq
    -- We now need a positive loop at s to get a length>0 path
    have hdiag : 0 < A s s := by
      simpa [A] using RScol_diag_pos (NN:=NN) (spec:=spec) (p:=p) (T:=T) s
    -- positive entry ⇒ ∃ path of positive length
    exact (Matrix.path_exists_of_pos_entry (A:=A) (i:=s) (j:=s) hdiag)
  · -- n > 0: convert positive entry of A^n into a path of length n
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hzero
    have hA_nonneg : ∀ i j, 0 ≤ A i j :=
      RScol_nonneg (NN:=NN) (spec:=spec) (p:=p) (T:=T)
    -- Convert positivity of a power entry into a positive-length quiver path.
    have hpath :
        Nonempty {q : Quiver.Path s s' // q.length = n} := by
      -- `pow_apply_pos_iff_nonempty_path` is the Mathlib lemma linking powers to paths.
      simpa using
        (Matrix.pow_apply_pos_iff_nonempty_path (A := A) (hA := hA_nonneg) n s s').1 hpos
    rcases hpath with ⟨⟨p, hp_len⟩⟩
    -- n > 0 ⇒ path length > 0
    have hp_len_pos : p.length > 0 := by
      simpa [hp_len] using hn_pos
    exact ⟨p, hp_len_pos⟩

/-- PF uniqueness of the stationary vector in the simplex for the random-scan kernel. -/
theorem RScol_uniqueStationarySimplex :
  ∃! (v : stdSimplex ℝ NN.State),
    (RScol (NN:=NN) (spec:=spec) p T) *ᵥ v.val = v.val := by
  have h_irred := RScol_irred (NN:=NN) (spec:=spec) p T
  have h_col : ∀ j, ∑ i, RScol (NN:=NN) (spec:=spec) p T i j = 1 :=
    RScol_colsum_one (NN:=NN) (spec:=spec) p T
  exact exists_positive_eigenvector_of_irreducible_stochastic h_irred h_col

/-- Ergodicity: random-scan is aperiodic and irreducible; the Boltzmann law is the
unique stationary distribution. -/
theorem randomScan_ergodicUniqueInvariant :
  ProbabilityTheory.Kernel.IsReversible (κ)
    ((HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).μProd T)
  ∧ (∀ s, 0 < RScol (NN:=NN) (spec:=spec) p T s s)
  ∧ Matrix.IsIrreducible (RScol (NN:=NN) (spec:=spec) p T)
  ∧ ∃! (v : stdSimplex ℝ NN.State),
        (RScol (NN:=NN) (spec:=spec) p T) *ᵥ v.val = v.val := by
  refine ⟨?rev, ?diag, ?irr, ?uniq⟩
  · exact randomScanKernel_reversible (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  · exact RScol_diag_pos (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  · exact RScol_irred (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  · exact RScol_uniqueStationarySimplex (NN:=NN) (spec:=spec) (p:=p) (T:=T)

/-
  MCMC.Finite integration (row-stochastic convention).

  `RScol` is column-stochastic (destination, source). `MCMC.Finite.IsStochastic` expects
  row-stochastic (source, destination), so we work with the transpose `RSrow = RScolᵀ`.
-/

/-- Row-stochastic transition matrix corresponding to `randomScanKernel`. -/
noncomputable def RSrow (NN : NeuralNetwork ℝ U σ)
    [Fintype NN.State] [DecidableEq NN.State] [Nonempty NN.State]
    [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
    (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature) :
    Matrix NN.State NN.State ℝ :=
  (RScol (NN:=NN) (spec:=spec) p T)ᵀ

lemma RSrow_isStochastic :
    MCMC.Finite.IsStochastic (RSrow (NN:=NN) (spec:=spec) p T) := by
  classical
  constructor
  · intro i j
    -- entrywise nonneg from RScol_nonneg
    simpa [RSrow, Matrix.transpose_apply] using
      (RScol_nonneg (NN:=NN) (spec:=spec) (p:=p) (T:=T) j i)
  · intro i
    -- row sum of RSrow is column sum of RScol
    simpa [RSrow, Matrix.transpose_apply] using
      (RScol_colsum_one (NN:=NN) (spec:=spec) (p:=p) (T:=T) i)

lemma RSrow_irred :
    Matrix.IsIrreducible (RSrow (NN:=NN) (spec:=spec) p T) := by
  -- irreducible is invariant under transpose
  simpa [RSrow] using (Matrix.IsIrreducible.transpose (A := RScol (NN:=NN) (spec:=spec) p T)
    (RScol_irred (NN:=NN) (spec:=spec) (p:=p) (T:=T)))

lemma RSrow_primitive :
    Matrix.IsPrimitive (RSrow (NN:=NN) (spec:=spec) p T) := by
  classical
  -- `IsPrimitive` from nonneg + irreducible + positive diagonal
  refine Matrix.IsPrimitive.of_irreducible_pos_diagonal
    (A := RSrow (NN:=NN) (spec:=spec) p T) ?_ (RSrow_irred (NN:=NN) (spec:=spec) (p:=p) (T:=T)) ?_
  · intro i j
    -- nonneg already shown in stochasticity proof
    exact (RSrow_isStochastic (spec:=spec) (p:=p) (T:=T)).1 i j
  · intro i
    -- diagonal positivity transfers across transpose
    simpa [RSrow, Matrix.transpose_apply] using
      (RScol_diag_pos (NN:=NN) (spec:=spec) (p:=p) (T:=T) i)

theorem RSrow_exists_unique_stationary_distribution :
    ∃! (π : stdSimplex ℝ NN.State),
      MCMC.Finite.IsStationary (RSrow (NN:=NN) (spec:=spec) p T) π := by
  classical
  exact MCMC.Finite.exists_unique_stationary_distribution_of_irreducible
    (n := NN.State)
    (h_stoch := RSrow_isStochastic (spec:=spec) (p:=p) (T:=T))
    (h_irred := RSrow_irred (spec:=spec) (p:=p) (T:=T))

/-!
## Identifying the stationary distribution as the Boltzmann law

We already have:
- kernel reversibility of `randomScanKernel` w.r.t. the Boltzmann measure `μProd` (in `DetailedBalanceBM`),
- uniqueness of the stationary distribution for `RSrow` (via `MCMC.Finite`).

Here we connect the two by showing that:
1. the matrix-induced kernel for `RSrow` agrees with `randomScanKernel`,
2. the vector-to-measure for the Boltzmann probability vector agrees with `μProd`,
3. hence the Boltzmann vector is stationary for `RSrow`,
4. hence it is the unique stationary distribution.
-/

section IdentifyStationary

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable (NN : NeuralNetwork ℝ U σ)
  [Fintype NN.State] [DecidableEq NN.State] [Nonempty NN.State]
  [TwoStateNeuralNetwork NN] [TwoStateExclusive NN]
  (spec : TwoState.EnergySpec' (NN:=NN)) (p : Params NN) (T : Temperature)

noncomputable abbrev κKernel : Kernel NN.State NN.State :=
  randomScanKernel (NN:=NN) spec p T

-- Discrete measurable structure (all sets measurable).
local instance : MeasurableSpace NN.State := ⊤
local instance : MeasurableSingletonClass NN.State := ⟨fun _ => trivial⟩

/-- The Boltzmann probability **measure** (`μProd`) for this finite Hopfield/Boltzmann setup. -/
noncomputable abbrev μBoltz : Measure NN.State :=
  (HopfieldBoltzmann.CEparams (NN:=NN) (spec:=spec) p).μProd T

private lemma μBoltz_singleton_ne_top (s : NN.State) :
    μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s} ≠ (⊤ : ℝ≥0∞) := by
  -- singleton ≤ univ and `μBoltz univ = 1`
  haveI : IsProbabilityMeasure (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) := by
    infer_instance
  have hle :
      μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s}
        ≤ μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) (Set.univ : Set NN.State) :=
    measure_mono (by intro x hx; trivial)
  have huniv :
      μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) (Set.univ : Set NN.State) = 1 := by
    simp
  have : μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s} ≤ (1 : ℝ≥0∞) := by
    simpa [huniv] using hle
  exact ne_of_lt (lt_of_le_of_lt this (by simp))

private lemma μBoltz_univ_eq_sum_singletons :
    μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) (Set.univ : Set NN.State)
      = Finset.sum Finset.univ (fun s : NN.State =>
          μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s}) := by
  classical
  have hU :
      (⋃ s ∈ (Finset.univ : Finset NN.State), ({s} : Set NN.State)) = (Set.univ : Set NN.State) := by
    ext x; simp
  have hdisj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset NN.State) : Set NN.State)
        (fun s : NN.State => ({s} : Set NN.State)) := by
    intro a ha b hb hab
    exact Set.disjoint_singleton.2 hab
  -- avoid rewriting `μBoltz Set.univ` to `1` by `simp`: rewrite the union by hand
  have h :=
    (measure_biUnion_finset (μ := μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T))
      (s := (Finset.univ : Finset NN.State))
      (f := fun s : NN.State => ({s} : Set NN.State)) hdisj (by intro s hs; simp))
  -- Rewrite the goal's LHS away from `Set.univ` (to avoid `simp` rewriting it to `1`).
  rw [← hU]
  -- `h` has RHS `∑ s ∈ univ, ...`; simplify that to the plain `∑ s, ...`.
  simpa using h

private lemma measure_eq_sum_singletons (m : Measure NN.State) (S : Set NN.State) :
    m S = Finset.sum (Finset.univ.filter (fun s => s ∈ S)) (fun s : NN.State => m {s}) := by
  classical
  let F : Finset NN.State := Finset.univ.filter (fun s => s ∈ S)
  have hU : (⋃ s ∈ F, ({s} : Set NN.State)) = S := by
    ext x; simp [F]
  have hdisj :
      Set.PairwiseDisjoint (↑F : Set NN.State) (fun s : NN.State => ({s} : Set NN.State)) := by
    intro a ha b hb hab
    exact Set.disjoint_singleton.2 hab
  simpa [F, hU] using
    (measure_biUnion_finset (μ := m) (s := F)
      (f := fun s : NN.State => ({s} : Set NN.State)) hdisj (by intro s hs; simp))

/-- The Boltzmann probability **vector** (entries are `toReal` of singleton masses). -/
noncomputable def πBoltzVec : stdSimplex ℝ NN.State :=
{ val := fun s => (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s}).toReal
  property := by
    refine ⟨?_, ?_⟩
    · intro s; exact ENNReal.toReal_nonneg
    · classical
      haveI : IsProbabilityMeasure (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) := by
        infer_instance
      have hfin :
          ∀ s : NN.State, μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s} ≠ (⊤ : ℝ≥0∞) :=
        μBoltz_singleton_ne_top (NN:=NN) (spec:=spec) (p:=p) (T:=T)
      have hsum_toReal :
          (Finset.sum Finset.univ (fun s : NN.State =>
              (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s}).toReal))
            =
          (Finset.sum Finset.univ (fun s : NN.State =>
              μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s})).toReal := by
        simpa using
          (ENNReal.toReal_sum (s := (Finset.univ : Finset NN.State))
            (f := fun s : NN.State => μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s})
            (by intro s hs; exact hfin s)).symm
      have huniv : μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) (Set.univ : Set NN.State) = 1 := by
        simpa using (measure_univ : μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) Set.univ = 1)
      have huniv_sum := μBoltz_univ_eq_sum_singletons (NN:=NN) (spec:=spec) (p:=p) (T:=T)
      calc
        Finset.sum Finset.univ (fun s : NN.State =>
            (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s}).toReal)
            =
          (Finset.sum Finset.univ (fun s : NN.State =>
            μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s})).toReal := hsum_toReal
        _ =
          (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) (Set.univ : Set NN.State)).toReal := by
            simpa [huniv_sum]
        _ = 1 := by simpa [huniv]
}

private lemma vecToMeasure_singleton (s : NN.State) :
    MCMC.Finite.vecToMeasure (πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T)) {s}
      = ENNReal.ofReal ((πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T)).val s) := by
  classical
  have hs : MeasurableSet ({s} : Set NN.State) := measurableSet_singleton s
  unfold MCMC.Finite.vecToMeasure
  -- unfold the finite sum of Diracs and reduce to the `s`-term
  simp [hs, Measure.dirac_apply']
  -- now a pure finite sum over a singleton indicator
  rw [Finset.sum_eq_single s]
  · simp [Set.indicator_of_mem, Set.mem_singleton_iff]
  · intro t _ ht
    simp [Set.indicator_of_notMem, ht]
  · simp

private lemma vecToMeasure_eq_μBoltz :
    MCMC.Finite.vecToMeasure (πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T))
      = μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) := by
  classical
  ext S hS
  let F : Finset NN.State := Finset.univ.filter (fun s => s ∈ S)
  have h1 :
      (MCMC.Finite.vecToMeasure (πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T))) S
        = Finset.sum F (fun s : NN.State =>
            (MCMC.Finite.vecToMeasure (πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T))) {s}) := by
    simpa [F] using
      (measure_eq_sum_singletons
        (NN:=NN)
        (m := MCMC.Finite.vecToMeasure (πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T)))
        S)
  have h2 :
      (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) S
        = Finset.sum F (fun s : NN.State =>
            (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) {s}) := by
    simpa [F] using
      (measure_eq_sum_singletons
        (NN:=NN)
        (m := μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T))
        S)
  -- compare the two sums termwise
  rw [h1, h2]
  refine Finset.sum_congr rfl ?_
  intro s hsF
  -- singleton equality
  calc
    (MCMC.Finite.vecToMeasure (πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T))) {s}
        = ENNReal.ofReal ((πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T)).val s) := by
            simpa using (vecToMeasure_singleton (NN:=NN) (spec:=spec) (p:=p) (T:=T) s)
    _ = ENNReal.ofReal ((μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T) {s}).toReal) := rfl
    _ = (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) {s} := by
            simpa [ENNReal.ofReal_toReal, μBoltz_singleton_ne_top (NN:=NN) (spec:=spec) (p:=p) (T:=T) s]

private lemma matrixToKernel_singleton
    {P : Matrix NN.State NN.State ℝ} (hP : MCMC.Finite.IsStochastic P) (i j : NN.State) :
    (MCMC.Finite.matrixToKernel P hP) i {j} = ENNReal.ofReal (P i j) := by
  classical
  have hmeas : MeasurableSet ({j} : Set NN.State) := measurableSet_singleton j
  unfold MCMC.Finite.matrixToKernel
  -- `matrixToKernel` is a finite sum of Diracs in each row; evaluate on the singleton `{j}`
  change ((∑ x : NN.State, ENNReal.ofReal (P i x) • Measure.dirac x) : Measure NN.State) {j}
      = ENNReal.ofReal (P i j)
  simp [hmeas, Measure.dirac_apply']
  rw [Finset.sum_eq_single j]
  · simp [Set.indicator_of_mem, Set.mem_singleton_iff]
  · intro t _ ht
    simp [Set.indicator_of_notMem, ht]
  · simp

private lemma κ_singleton_ne_top (i j : NN.State) :
    (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) {j} ≠ (⊤ : ℝ≥0∞) := by
  -- {j} ⊆ univ, and κ i univ = 1 (since κ i is a PMF.toMeasure)
  have hle :
      (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) {j}
        ≤ (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) (Set.univ : Set NN.State) :=
    measure_mono (by intro x hx; trivial)
  -- match the `randomScanKernel` definition exactly (uses `uniformOfFinset univ`)
  let sitePMF : PMF U :=
    PMF.uniformOfFinset (Finset.univ) (by classical exact Finset.univ_nonempty)
  set q : PMF NN.State :=
    sitePMF.bind (fun u => TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T i u) with hq
  have hκ_eval : ∀ B, (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) B = q.toMeasure B := by
    intro B
    simp [κKernel, randomScanKernel, pmfToKernel, ProbabilityTheory.Kernel.ofFunOfCountable, sitePMF, hq]
  have huniv :
      (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) (Set.univ : Set NN.State) = 1 := by
    calc
      (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) Set.univ = q.toMeasure Set.univ := by
        simp [hκ_eval]
      _ = (1 : ℝ≥0∞) := by simp
  have : (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) {j} ≤ (1 : ℝ≥0∞) := by
    simpa [huniv] using hle
  exact ne_of_lt (lt_of_le_of_lt this (by simp))

private lemma matrixToKernel_RSrow_eq_κ :
    MCMC.Finite.matrixToKernel
        (RSrow (NN:=NN) (spec:=spec) p T)
        (RSrow_isStochastic (NN:=NN) (spec:=spec) (p:=p) (T:=T))
      = κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) := by
  classical
  ext i S hS
  let F : Finset NN.State := Finset.univ.filter (fun s => s ∈ S)
  have h1 :
      ((MCMC.Finite.matrixToKernel
          (RSrow (NN:=NN) (spec:=spec) p T)
          (RSrow_isStochastic (NN:=NN) (spec:=spec) (p:=p) (T:=T)) i) S)
        = Finset.sum F (fun s : NN.State =>
            ((MCMC.Finite.matrixToKernel
              (RSrow (NN:=NN) (spec:=spec) p T)
              (RSrow_isStochastic (NN:=NN) (spec:=spec) (p:=p) (T:=T)) i) {s})) := by
    simpa [F] using
      (measure_eq_sum_singletons
        (NN:=NN)
        (m := (MCMC.Finite.matrixToKernel
          (RSrow (NN:=NN) (spec:=spec) p T)
          (RSrow_isStochastic (NN:=NN) (spec:=spec) (p:=p) (T:=T)) i))
        S)
  have h2 :
      ((κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) S)
        = Finset.sum F (fun s : NN.State =>
            ((κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) {s})) := by
    simpa [F] using
      (measure_eq_sum_singletons
        (NN:=NN)
        (m := (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i))
        S)
  -- compare the two sums termwise
  rw [h1, h2]
  refine Finset.sum_congr rfl ?_
  · intro j hjF
    have : j ∈ S := by
      simpa [F, Finset.mem_filter] using hjF
    -- singleton equality
    have hfin : (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) {j} ≠ (⊤ : ℝ≥0∞) :=
      κ_singleton_ne_top (NN:=NN) (spec:=spec) (p:=p) (T:=T) i j
    calc
      ((MCMC.Finite.matrixToKernel
          (RSrow (NN:=NN) (spec:=spec) p T)
          (RSrow_isStochastic (NN:=NN) (spec:=spec) (p:=p) (T:=T))) i) {j}
          = ENNReal.ofReal (RSrow (NN:=NN) (spec:=spec) p T i j) := by
              simpa using
                (matrixToKernel_singleton (NN:=NN) (P := RSrow (NN:=NN) (spec:=spec) p T)
                  (hP := RSrow_isStochastic (NN:=NN) (spec:=spec) (p:=p) (T:=T)) i j)
      _ = ENNReal.ofReal ((κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) {j}).toReal := by
              simp [RSrow, RScol, κKernel, Matrix.transpose_apply]
      _ = (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T) i) {j} := by
              simpa [ENNReal.ofReal_toReal, hfin]

theorem πBoltzVec_is_stationary_RSrow :
    MCMC.Finite.IsStationary (RSrow (NN:=NN) (spec:=spec) p T)
      (πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T)) := by
  classical
  have hP : MCMC.Finite.IsStochastic (RSrow (NN:=NN) (spec:=spec) p T) :=
    RSrow_isStochastic (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  -- kernel invariance from reversibility
  have hrev :
      ProbabilityTheory.Kernel.IsReversible (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T))
        (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) :=
    randomScanKernel_reversible (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  haveI : ProbabilityTheory.IsMarkovKernel (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T)) := by
    classical
    refine ⟨?_⟩
    intro x
    unfold κKernel randomScanKernel pmfToKernel
    -- `Kernel.ofFunOfCountable` is definitional on application
    simpa [ProbabilityTheory.Kernel.ofFunOfCountable] using
      (inferInstance : IsProbabilityMeasure
        ((PMF.uniformOfFinset (Finset.univ) (by simp)).bind
          (fun u =>
            TwoState.gibbsUpdate (NN:=NN) (RingHom.id ℝ) p T x u)).toMeasure)
  have hinvκ :
      ProbabilityTheory.Kernel.Invariant (κKernel (NN:=NN) (spec:=spec) (p:=p) (T:=T))
        (μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)) :=
    hrev.invariant
  -- transport invariance across equal kernel/measure
  have hk_eq := matrixToKernel_RSrow_eq_κ (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  have hμ_eq := vecToMeasure_eq_μBoltz (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  rw [MCMC.Finite.isStationary_iff_invariant
    (P := RSrow (NN:=NN) (spec:=spec) p T)
    (π := πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T)) hP]
  simpa [hk_eq, hμ_eq] using hinvκ

theorem RSrow_stationary_unique_eq_πBoltzVec :
    (Classical.choose
      (RSrow_exists_unique_stationary_distribution (NN:=NN) (spec:=spec) (p:=p) (T:=T)).exists)
      = πBoltzVec (NN:=NN) (spec:=spec) (p:=p) (T:=T) := by
  classical
  have huniq := RSrow_exists_unique_stationary_distribution (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  have hstat := πBoltzVec_is_stationary_RSrow (NN:=NN) (spec:=spec) (p:=p) (T:=T)
  exact huniq.unique (Classical.choose_spec huniq.exists) hstat

end IdentifyStationary

end Ergodicity
