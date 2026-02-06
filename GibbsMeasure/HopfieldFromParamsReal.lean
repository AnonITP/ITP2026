import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent

import NeuralNetwork.NeuralNetwork.Core

/-!
## Hopfield parameters → Georgii potential (real spins)

This is the “spin-type aligned” version of `GibbsMeasure.HopfieldFromParams`:
we build a Georgii potential on configurations `U → ℝ`, so it can be compared directly with
Hopfield energies computed from Hopfield states `s : (HopfieldNetwork ℝ U).State` (where `s.act : U → ℝ`).

We deliberately keep the definition **choice-free** on supports:
- singleton supports (`Δ.card = 1`) encode the external field / thresholds,
- pair supports (`Δ.card = 2`) encode the quadratic interaction term via a symmetric double sum over `Δ.attach`.

This file only provides the potential + finitary instance; measurability (`IsPotential`) is not needed
for the energy-equality bridge itself and can be added later when moving to infinite-volume theory.
-/

open scoped BigOperators

namespace GibbsMeasure.Examples.HopfieldFromParamsReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

/-- Extract the real threshold scalar `θ' (θ u)` from Hopfield parameters. -/
noncomputable def θu (p : Params (HopfieldNetwork ℝ U)) (u : U) : ℝ :=
  θ' (p.θ u)

/-- Georgii potential on real-spin configurations `U → ℝ`, induced by Hopfield parameters `(w, θ)`. -/
noncomputable def hopfieldPotentialFromParamsR (p : Params (HopfieldNetwork ℝ U)) :
    Potential U ℝ :=
  fun Δ η =>
    if Δ.card = 2 then
      (- (1 / 2 : ℝ)) *
        (Δ.attach.sum fun i =>
          (Δ.attach.sum fun j =>
            if j.1 ≠ i.1 then
              (p.w i.1 j.1) * (η i.1) * (η j.1)
            else 0))
    else if Δ.card = 1 then
      Δ.attach.sum fun i => (θu (U := U) p i.1) * (η i.1)
    else
      0

instance (p : Params (HopfieldNetwork ℝ U)) :
    Potential.IsFinitary (hopfieldPotentialFromParamsR (U := U) p) where
  finite_support := by
    classical
    -- Supports are only singletons or pairs, hence finite.
    let s1 : Finset (Finset U) := Finset.univ.image (fun i : U => ({i} : Finset U))
    let s2 : Finset (Finset U) :=
      Finset.univ.biUnion fun i : U =>
        (Finset.univ.erase i).image (fun j : U => ({i, j} : Finset U))
    let s : Finset (Finset U) := s1 ∪ s2
    apply Set.Finite.subset (s := (s : Set (Finset U)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      -- If `Φ Δ ≠ 0`, then `Δ.card = 1` or `Δ.card = 2`.
      have hcard : Δ.card = 1 ∨ Δ.card = 2 := by
        by_contra hcard
        have hne1 : Δ.card ≠ 1 := by intro h1; exact hcard (Or.inl h1)
        have hne2 : Δ.card ≠ 2 := by intro h2; exact hcard (Or.inr h2)
        have hzero : hopfieldPotentialFromParamsR (U := U) p Δ = 0 := by
          funext η
          simp [hopfieldPotentialFromParamsR, hne2, hne1]
        exact hΔ hzero
      -- Now `Δ` is a singleton or a pair, hence belongs to `s`.
      cases hcard with
      | inl h1 =>
          rcases Finset.card_eq_one.1 h1 with ⟨i, rfl⟩
          have : ({i} : Finset U) ∈ s1 := by simp [s1]
          have : ({i} : Finset U) ∈ s := by simp [s, this]
          simpa using this
      | inr h2 =>
          rcases Finset.card_eq_two.1 h2 with ⟨i, j, hij, rfl⟩
          have : ({i, j} : Finset U) ∈ s2 := by
            have hj : j ∈ Finset.univ.erase i := by simp [Finset.mem_erase, hij.symm]
            have himg :
                ({i, j} : Finset U) ∈ (Finset.univ.erase i).image (fun k : U => ({i, k} : Finset U)) := by
              refine Finset.mem_image.2 ?_
              exact ⟨j, hj, rfl⟩
            refine Finset.mem_biUnion.2 ?_
            refine ⟨i, by simp, ?_⟩
            simpa [s2] using himg
          have : ({i, j} : Finset U) ∈ s := by simp [s, this]
          simpa using this

end GibbsMeasure.Examples.HopfieldFromParamsReal

namespace GibbsMeasure.Examples.HopfieldFromParamsReal

open scoped BigOperators
open MeasureTheory

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

private lemma measurable_finset_sum {α β : Type*} [MeasurableSpace β] {s : Finset α}
    {f : α → β → ℝ} (hf : ∀ a ∈ s, Measurable (f a)) :
    Measurable (fun x : β => s.sum (fun a => f a x)) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    simp
  · intro a s ha ih hf
    have hfa : Measurable (f a) := hf a (by simp [ha])
    have hfs : ∀ b ∈ s, Measurable (f b) := by
      intro b hb
      exact hf b (by simp [hb])
    have ih' : Measurable (fun x : β => s.sum (fun b => f b x)) := ih hfs
    simpa [Finset.sum_insert, ha] using hfa.add ih'

/-- The params-induced real-spin potential is an admissible (Georgii) potential. -/
instance (p : Params (HopfieldNetwork ℝ U)) :
    Potential.IsPotential (hopfieldPotentialFromParamsR (U := U) p) where
  measurable Δ := by
    classical
    -- Factor through the restriction map `U → ℝ → Δ → ℝ`.
    let Δset : Set U := (Δ : Set U)
    -- Define `g : (Δ → ℝ) → ℝ` so that `Φ Δ = g ∘ restrict Δ`.
    let g : (Δ → ℝ) → ℝ := fun τ =>
      if h2 : Δ.card = 2 then
        (- (1 / 2 : ℝ)) *
          (Δ.attach.sum fun i =>
            Δ.attach.sum fun j =>
              if j.1 ≠ i.1 then
                (p.w i.1 j.1) *
                  (τ ⟨i.1, i.2⟩) *
                  (τ ⟨j.1, j.2⟩)
              else 0)
      else if h1 : Δ.card = 1 then
        Δ.attach.sum fun i =>
          (θu (U := U) p i.1) * (τ ⟨i.1, i.2⟩)
      else
        0
    have hg : Measurable g := by
      -- Measurability is by finite sums/products of coordinate projections on the finite product space `Δ → ℝ`.
      classical
      by_cases h2 : Δ.card = 2
      · -- pair term
        have hinner :
            ∀ i : {x // x ∈ Δ}, Measurable (fun τ : (Δ → ℝ) =>
              (Δ.attach.sum fun j =>
                if (j.1 : U) ≠ (i.1 : U) then
                  (p.w (i.1 : U) (j.1 : U)) *
                    (τ ⟨i.1, i.2⟩) *
                    (τ ⟨j.1, j.2⟩)
                else 0)) := by
          intro i
          refine measurable_finset_sum (s := Δ.attach) (β := (Δ → ℝ))
              (f := fun j τ =>
                if (j.1 : U) ≠ (i.1 : U) then
                  (p.w (i.1 : U) (j.1 : U)) *
                    (τ ⟨i.1, i.2⟩) *
                    (τ ⟨j.1, j.2⟩)
                else 0) ?_
          intro j hj
          by_cases hji : (j.1 : U) ≠ (i.1 : U)
          · have hi : Measurable (fun τ : (Δ → ℝ) => τ ⟨i.1, i.2⟩) := by
              simpa using (measurable_pi_apply (⟨i.1, i.2⟩ : Δ))
            have hj' : Measurable (fun τ : (Δ → ℝ) => τ ⟨j.1, j.2⟩) := by
              simpa using (measurable_pi_apply (⟨j.1, j.2⟩ : Δ))
            simpa [hji, mul_assoc] using (measurable_const.mul (hi.mul hj'))
          · simp [hji]
        have houter : Measurable (fun τ : (Δ → ℝ) =>
            Δ.attach.sum fun i =>
              (Δ.attach.sum fun j =>
                if j.1 ≠ i.1 then
                  (p.w i.1 j.1) *
                    (τ ⟨i.1, i.2⟩) *
                    (τ ⟨j.1, j.2⟩)
                else 0)) := by
          refine measurable_finset_sum (s := Δ.attach) (β := (Δ → ℝ))
              (f := fun i τ =>
                (Δ.attach.sum fun j =>
                  if j.1 ≠ i.1 then
                    (p.w i.1 j.1) *
                      (τ ⟨i.1, i.2⟩) *
                      (τ ⟨j.1, j.2⟩)
                  else 0)) ?_
          intro i hi
          -- `hinner` already proves measurability of the inner sum
          simpa using hinner i
        -- assemble
        simpa [g, h2] using (measurable_const.mul houter)
      · by_cases h1 : Δ.card = 1
        · -- singleton term
          have hsum : Measurable (fun τ : (Δ → ℝ) =>
              Δ.attach.sum fun i =>
                (θu (U := U) p i.1) * (τ ⟨i.1, i.2⟩)) := by
            refine measurable_finset_sum (s := Δ.attach) (β := (Δ → ℝ))
                (f := fun i τ =>
                  (θu (U := U) p i.1) * (τ ⟨i.1, i.2⟩)) ?_
            intro i hi
            have hi' : Measurable (fun τ : (Δ → ℝ) => τ ⟨i.1, i.2⟩) := by
              simpa using (measurable_pi_apply (⟨i.1, i.2⟩ : Δ))
            simpa [mul_assoc] using (measurable_const.mul hi')
          simpa [g, h2, h1] using hsum
        · -- zero term
          simp [g, h2, h1]
    have hres :
        Measurable[cylinderEvents (X := fun _ : U ↦ ℝ) Δset]
          (Set.restrict (π := fun _ : U ↦ ℝ) Δset) :=
      MeasureTheory.measurable_restrict_cylinderEvents (X := fun _ : U ↦ ℝ) Δset
    have hfac :
        hopfieldPotentialFromParamsR (U := U) p Δ =
          fun η : U → ℝ => g (Set.restrict (π := fun _ : U ↦ ℝ) Δset η) := by
      funext η
      by_cases h2 : Δ.card = 2
      · simp [hopfieldPotentialFromParamsR, g, h2, Δset, Finset.attach]
      · by_cases h1 : Δ.card = 1
        · simp [hopfieldPotentialFromParamsR, g, h1, Δset, Finset.attach]
        · simp [hopfieldPotentialFromParamsR, g, h2, h1, Δset]
    simpa [hfac] using (hg.comp hres)

/-- Georgii Gibbs specification induced by Hopfield parameters `(w, θ)` on real spins, at inverse temperature `β`. -/
noncomputable def hopfieldSpecificationFromParamsR
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset U) (η : U → ℝ),
      Specification.premodifierZ ν
        (Potential.boltzmannWeight (Φ := hopfieldPotentialFromParamsR (U := U) p) β) Λ η ≠ ⊤) :
    Specification U ℝ :=
  Potential.gibbsSpecification (hopfieldPotentialFromParamsR (U := U) p) β ν hZ

end GibbsMeasure.Examples.HopfieldFromParamsReal
