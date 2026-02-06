import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent

import NeuralNetwork.NeuralNetwork.Core

/-!
## HopfieldNetwork → Georgii potential/specification (from parameters)

This is the principled bridge layer: it constructs a Georgii-style finitary potential and
Gibbs specification **directly from Hopfield parameters** (`w` and `θ`), matching the Hopfield
energy decomposition in `NeuralNetwork.NeuralNetwork.Core`:

- pair interactions from weights (off-diagonal, symmetric),
- singleton interactions from thresholds (external field).

This file is designed so that the key equality lemma

`Hopfield energy = Potential.interactingHamiltonian`

can be stated and proved without any ad-hoc choices.
-/

open ENNReal MeasureTheory
open scoped BigOperators

namespace GibbsMeasure.Examples.HopfieldFromParams

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

-- configuration space for Georgii-side Hopfield: spins as `Int` (as in the SK example)
instance : MeasurableSpace Int := ⊤

/-!
### Potential induced by Hopfield parameters

We model weights via a pair potential supported on `Δ.card = 2`:

`Φ {i,j} σ = - (w i j) * σ i * σ j`

and thresholds via a singleton potential supported on `Δ.card = 1`:

`Φ {i} σ = (θ i) * σ i`

The signs are chosen to match `NeuralNetwork.State.Ew` and `NeuralNetwork.State.Eθ`
in `NeuralNetwork.NeuralNetwork.Core` (up to the ubiquitous constant/diagonal convention).
-/

/-- Extract the real threshold `θ' (θ u)` from the Hopfield parameter vector. -/
noncomputable def θu (p : Params (HopfieldNetwork ℝ U)) (u : U) : ℝ :=
  θ' (p.θ u)

noncomputable def hopfieldPotentialFromParams (p : Params (HopfieldNetwork ℝ U)) :
    Potential U Int :=
  fun Δ σ =>
    if Δ.card = 2 then
      (- (1 / 2 : ℝ)) *
        (Δ.attach.sum fun i =>
          (Δ.attach.sum fun j =>
            if j.1 ≠ i.1 then
              (p.w i.1 j.1) * (σ i.1 : ℝ) * (σ j.1 : ℝ)
            else 0))
    else if Δ.card = 1 then
      -- singleton/external field term (choice-free: sum over the singleton support)
      Δ.attach.sum fun i => (θu (p := p) i.1) * (σ i.1 : ℝ)
    else
      0

instance (p : Params (HopfieldNetwork ℝ U)) :
    Potential.IsFinitary (hopfieldPotentialFromParams p) where
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
        have hne1 : Δ.card ≠ 1 := by
          intro h1; exact hcard (Or.inl h1)
        have hne2 : Δ.card ≠ 2 := by
          intro h2; exact hcard (Or.inr h2)
        have hzero : hopfieldPotentialFromParams p Δ = 0 := by
          funext σ
          simp [hopfieldPotentialFromParams, hne2, hne1]
        exact hΔ hzero
      -- Now `Δ` is a singleton or a pair, hence belongs to `s`.
      cases hcard with
      | inl h1 =>
          rcases Finset.card_eq_one.1 h1 with ⟨i, rfl⟩
          have : ({i} : Finset U) ∈ s1 := by simp [s1]
          exact by
            have : ({i} : Finset U) ∈ s := by
              simp [s, this]
            simpa using this
      | inr h2 =>
          rcases Finset.card_eq_two.1 h2 with ⟨i, j, hij, rfl⟩
          have : ({i, j} : Finset U) ∈ s2 := by
            have hj : j ∈ Finset.univ.erase i := by
              -- `j ≠ i` is `hij.symm`.
              simp [Finset.mem_erase, hij.symm]
            have himg :
                ({i, j} : Finset U) ∈ (Finset.univ.erase i).image (fun k : U => ({i, k} : Finset U)) := by
              refine Finset.mem_image.2 ?_
              exact ⟨j, hj, rfl⟩
            -- Now lift through the `biUnion` over `i ∈ univ`.
            refine Finset.mem_biUnion.2 ?_
            refine ⟨i, by simp, ?_⟩
            simpa [s2] using himg
          exact by
            have : ({i, j} : Finset U) ∈ s := by
              simp [s, this]
            simpa using this

instance (p : Params (HopfieldNetwork ℝ U)) :
    Potential.IsPotential (hopfieldPotentialFromParams p) where
  measurable Δ := by
    classical
    -- Factor through the restriction map `Set.restrict Δ`.
    let Δset : Set U := (Δ : Set U)
    let g : (Δset → Int) → ℝ := fun τ =>
      if h2 : Δ.card = 2 then
        (- (1 / 2 : ℝ)) *
          (Δ.attach.sum fun i =>
            (Δ.attach.sum fun j =>
              if j.1 ≠ i.1 then
                (p.w i.1 j.1) *
                  (τ ⟨i.1, by simp [Δset]⟩ : ℝ) *
                  (τ ⟨j.1, by simp [Δset]⟩ : ℝ)
              else 0))
      else if h1 : Δ.card = 1 then
        Δ.attach.sum fun i =>
          (θu (p := p) i.1) * (τ ⟨i.1, by simp [Δset]⟩ : ℝ)
      else
        0
    have hg : Measurable g := by
      -- `MeasurableSpace Int = ⊤` ⇒ `MeasurableSpace (Δ → Int) = ⊤` ⇒ every `g` is measurable.
      simp [g]; exact Measurable.of_discrete
    have hres :
        Measurable[cylinderEvents (X := fun _ : U ↦ Int) Δset]
          (Set.restrict (π := fun _ : U ↦ Int) Δset) :=
      MeasureTheory.measurable_restrict_cylinderEvents (X := fun _ : U ↦ Int) Δset
    have hfac :
        hopfieldPotentialFromParams p Δ =
          fun σ : U → Int => g (Set.restrict (π := fun _ : U ↦ Int) Δset σ) := by
      funext σ
      -- Unfold both sides; `Set.restrict` just reads the corresponding coordinate.
      by_cases h2 : Δ.card = 2
      · simp [hopfieldPotentialFromParams, g, h2, Δset, Finset.attach]
      · by_cases h1 : Δ.card = 1
        · simp [hopfieldPotentialFromParams, g, h1, Δset, Finset.attach]
        · simp [hopfieldPotentialFromParams, g, h2, h1, Δset]
    simpa [hfac] using (hg.comp hres)

/-- Georgii Gibbs specification induced by Hopfield parameters `(w, θ)` at inverse temperature `β`. -/
noncomputable def hopfieldSpecificationFromParams
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (ν : Measure Int)
    [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset U) (η : U → Int),
      Specification.premodifierZ ν (Potential.boltzmannWeight (Φ := hopfieldPotentialFromParams p) β) Λ η ≠ ⊤) :
    Specification U Int :=
  Potential.gibbsSpecification (hopfieldPotentialFromParams p) β ν hZ

end GibbsMeasure.Examples.HopfieldFromParams
