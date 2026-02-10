import ThreeD.Core
import ThreeD.Invariant
import GibbsMeasure.Specification

/-!
## Bridge: GibbsMeasure.Specification → ThreeD indexed stochastic dynamics (infinite lattices)

In the Georgii/DLR `GibbsMeasure` approach, a **specification**

`γ : Specification S E`

is a family of boundary-condition kernels indexed by finite volumes `Λ : Finset S`:

`γ Λ : Kernel[cylinderEvents Λᶜ] (S → E) (S → E)`.

For the ThreeD vocabulary, we want an actual Markov kernel on the full measurable space `S → E`.
We obtain it via `Kernel.comap id cylinderEvents_le_pi`, exactly as in the consistency definition.
-/

namespace NeuralNetwork

namespace ThreeD

namespace Bridges

namespace GibbsMeasure

open ProbabilityTheory MeasureTheory Set

variable {S E : Type*} [MeasurableSpace E]

/-- The full measurable-space kernel associated to a specification kernel `γ Λ`. -/
noncomputable def kernelFull (γ : _root_.Specification S E) (Λ : Finset S) :
    ProbabilityTheory.Kernel (S → E) (S → E) :=
  (γ Λ).comap id cylinderEvents_le_pi

/-- View a specification as ThreeD indexed stochastic dynamics with index `Finset S` and no parameters. -/
noncomputable def toIndexedStochasticDynamics (γ : _root_.Specification S E) :
    ThreeD.IndexedStochasticDynamics (Finset S) PUnit (S → E) where
  K := fun Λ _ => kernelFull (S := S) (E := E) γ Λ

/-!
### Fixed-point characterization (Gibbs measures as invariants)

Your `GibbsMeasure/Specification.lean` already proves:

`IsGibbsMeasure γ μ ↔ ∀ Λ, μ.bind (γ Λ) = μ`

under `γ.IsProper` + `γ.IsMarkov` + finiteness assumptions.

In the ThreeD view, this says “a Gibbs measure is invariant for every local kernel”.
We keep this lemma here as a convenient re-export with `kernelFull`.
-/

lemma isGibbsMeasure_iff_forall_bind_kernelFull
    {γ : _root_.Specification S E} {μ : MeasureTheory.Measure (S → E)}
    (hγ : Specification.IsProper γ) [MeasureTheory.IsFiniteMeasure μ]
    [Specification.IsMarkov γ] :
    Specification.IsGibbsMeasure (S := S) (E := E) γ μ
      ↔
      ∀ Λ : Finset S, μ.bind (kernelFull (S := S) (E := E) γ Λ) = μ := by
  classical
  simpa [kernelFull] using
    (Specification.isGibbsMeasure_iff_forall_bind_eq
      (S := S) (E := E) (γ := γ) (μ := μ) hγ)

/-| In ThreeD terms: a Gibbs measure is stationary for all local kernels (all finite volumes). -/
lemma isGibbsMeasure_iff_stationaryIndexed_kernelFull
    {γ : _root_.Specification S E} {μ : MeasureTheory.Measure (S → E)}
    (hγ : Specification.IsProper γ) [MeasureTheory.IsFiniteMeasure μ]
    [Specification.IsMarkov γ] :
    Specification.IsGibbsMeasure (S := S) (E := E) γ μ
      ↔
      ThreeD.IsStationaryIndexed
        (Θ := PUnit) (ι := Finset S) (X := (S → E))
        (toIndexedStochasticDynamics (S := S) (E := E) γ) PUnit.unit μ := by
  simpa [ThreeD.IsStationaryIndexed, Bridges.GibbsMeasure.toIndexedStochasticDynamics,
    kernelFull, ProbabilityTheory.Kernel.Invariant] using
    (isGibbsMeasure_iff_forall_bind_kernelFull (S := S) (E := E) (γ := γ) (μ := μ) hγ)

end GibbsMeasure

end Bridges

end ThreeD

end NeuralNetwork
