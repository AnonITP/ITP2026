import GibbsMeasure.Potential
import GibbsMeasure.Specification
import GibbsMeasure.Prereqs.Filtration.Consistent
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
## Hopfield model as a Georgii potential / Gibbs specification (non-orthogonal patterns)

This file starts the **Georgii-side** Hopfield pipeline, in direct analogy with
`GibbsMeasure/SpinGlass.lean`.

Key design choice (Talagrand / mean-field Hopfield):
- spins take values in `{±1}` (we use `Int` for the configuration space, like the SK example),
- the interaction is pairwise with couplings

\[
J_{ij} := \frac{1}{|V|} \sum_{\mu=1}^m \xi_i^\mu \xi_j^\mu,
\]

with **no orthogonality assumption** on the patterns `ξ`. The resulting crosstalk/interference is
encoded in the couplings, and later analysis can reuse the “signal + interference” algebra already
formalized on the HopfieldNet side.

The potential is the standard pair interaction:
\[
\Phi_{\{i,j\}}(\sigma) = - J_{ij} \, \sigma_i \sigma_j
\]
and zero on all other finite supports.
-/

open ENNReal MeasureTheory

namespace GibbsMeasure.Examples.Hopfield

variable {V : Type*} [DecidableEq V] [Fintype V]

-- Make `Int` measurable (trivial σ-algebra), matching the SpinGlass example.
instance : MeasurableSpace Int := ⊤

open scoped BigOperators

/-! ### Hebbian couplings from patterns (no orthogonality assumptions) -/

variable {m : ℕ}

/-- Hopfield patterns: `m` stored patterns, each a configuration in `{±1}^V`. -/
abbrev Patterns (V : Type*) (m : ℕ) := Fin m → V → Int

/-- The (mean-field normalized) Hopfield coupling \(J_{ij}\) induced by patterns `ξ`. -/
noncomputable def hopfieldJ (ξ : Patterns V m) (i j : V) : ℝ :=
  (1 / (Fintype.card V : ℝ)) *
    ∑ μ : Fin m, (ξ μ i : ℝ) * (ξ μ j : ℝ)

/-! ### Potential and specification -/

/-- Pairwise Hopfield potential on `{±1}^V` with couplings from patterns `ξ`. -/
noncomputable def hopfieldPotential (ξ : Patterns V m) : Potential V Int :=
  fun Δ σ ↦
    -- Choice-free definition: use `Δ.card = 2` and a symmetric
    -- double sum over the support `Δ`, divided by 2 to avoid orientation dependence.
    if Δ.card = 2 then
      (- (1 / 2 : ℝ)) *
        (Δ.attach.sum fun i =>
          (Δ.attach.sum fun j =>
            if j.1 ≠ i.1 then
              hopfieldJ (V := V) (m := m) ξ i.1 j.1 * (σ i.1 : ℝ) * (σ j.1 : ℝ)
            else
              0))
    else
      0

instance (ξ : Patterns V m) : Potential.IsFinitary (hopfieldPotential (V := V) (m := m) ξ) where
  finite_support := by
    classical
    -- Same finitary support argument as the SK example: only 2-site interactions can be non-zero.
    let s : Finset (Finset V) :=
      Finset.univ.biUnion fun i ↦ Finset.univ.image (fun j ↦ ({i, j} : Finset V))
    apply Set.Finite.subset (s := (s : Set (Finset V)))
    · exact Finset.finite_toSet s
    · intro Δ hΔ
      -- If `hopfieldPotential ξ Δ ≠ 0`, then necessarily `Δ.card = 2`.
      have hcard : Δ.card = 2 := by
        by_contra hcard
        have hzero : hopfieldPotential (V := V) (m := m) ξ Δ = 0 := by
          funext σ
          simp [hopfieldPotential, hcard]
        exact hΔ hzero
      -- Hence `Δ` is some `{i,j}`.
      rcases Finset.card_eq_two.1 hcard with ⟨i, j, hij, rfl⟩
      simp [s]

instance (ξ : Patterns V m) : Potential.IsPotential (hopfieldPotential (V := V) (m := m) ξ) where
  measurable Δ := by
    classical
    -- Prove cylinder-measurability by factoring through the restriction map.
    -- This avoids any choice and aligns with the Georgii / cylinder-events semantics.
    let Δset : Set V := (Δ : Set V)
    -- Define the potential term as a function of the restricted configuration `τ : Δ → Int`.
    let g : (Δset → Int) → ℝ := fun τ =>
      if Δ.card = 2 then
        (- (1 / 2 : ℝ)) *
          (Δ.attach.sum fun i =>
            (Δ.attach.sum fun j =>
              if j.1 ≠ i.1 then
                hopfieldJ (V := V) (m := m) ξ i.1 j.1 *
                  (τ ⟨i.1, by simp [Δset]⟩ : ℝ) *
                  (τ ⟨j.1, by simp [Δset]⟩ : ℝ)
              else
                0))
      else 0
    have hg : Measurable g := by
      -- `MeasurableSpace Int = ⊤` ⇒ `MeasurableSpace (Δ → Int) = ⊤` ⇒ every `g` is measurable.
      simp [g]; exact Measurable.of_discrete
    have hres :
        Measurable[cylinderEvents (X := fun _ : V ↦ Int) Δset]
          (Set.restrict (π := fun _ : V ↦ Int) Δset) :=
      MeasureTheory.measurable_restrict_cylinderEvents (X := fun _ : V ↦ Int) Δset
    have hfac :
        hopfieldPotential (V := V) (m := m) ξ Δ =
          fun σ : V → Int => g (Set.restrict (π := fun _ : V ↦ Int) Δset σ) := by
      funext σ
      -- Unfold both sides and use the definition of `Set.restrict`.
      by_cases hcard : Δ.card = 2
      · simp [hopfieldPotential, g, hcard, Δset]
      · simp [hopfieldPotential, g, hcard, Δset]
    -- Conclude by composing `g` with the measurable restriction map.
    simpa [hfac] using (hg.comp hres)


/-- The Gibbs specification for the Hopfield model (Georgii API). -/
noncomputable def hopfieldSpecification
    (ξ : Patterns V m) (β : ℝ) (ν : Measure Int) [IsProbabilityMeasure ν]
    (hZ : ∀ (Λ : Finset V) (η : V → Int),
      Specification.premodifierZ ν
        (Potential.boltzmannWeight (Φ := hopfieldPotential (V := V) (m := m) ξ) β) Λ η ≠ ⊤) :
    Specification V Int :=
  Potential.gibbsSpecification (hopfieldPotential (V := V) (m := m) ξ) β ν hZ

end GibbsMeasure.Examples.Hopfield
