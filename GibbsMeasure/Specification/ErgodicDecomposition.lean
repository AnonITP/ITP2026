import GibbsMeasure.Specification.Extremal
import GibbsMeasure.Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Measure.Real

/-!
# Tail disintegration and ergodic decomposition setup (Georgii, Ch. 7 — setup)

This file introduces the **tail conditional kernel** using Mathlib's `ProbabilityTheory.condExpKernel`.

For a finite measure `μ` on the configuration space `S → E`, we define the kernel
`tailKernel μ : Kernel[𝓣] (S → E) (S → E)` (domain σ-algebra is the tail σ-algebra `𝓣`).

We record:

- the disintegration identity `tailKernel μ ∘ₘ μ.trim (𝓣 ≤ pi) = μ`;
- for tail events `A ∈ 𝓣`, the kernel evaluates `A` as the **indicator** (hence is {0,1}-valued a.e.).

These lemmas are the starting point for the ergodic (extremal) decomposition of Gibbs measures.
-/

open Set
open scoped ENNReal ProbabilityTheory
open ProbabilityTheory

namespace MeasureTheory

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ## Tail σ-algebra vs. the full product σ-algebra -/

lemma tailSigmaAlgebra_le_pi :
    (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi := by
  refine le_trans
    (iInf_le (fun Λ : Finset S =>
      cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) (∅ : Finset S)) ?_
  simp

/-! ## Tail conditional kernel -/

section TailKernel

variable (μ : Measure (S → E)) [IsFiniteMeasure μ]
variable [Countable S] [StandardBorelSpace E]

-- The configuration space is standard Borel as a countable product of standard Borel spaces.
instance : StandardBorelSpace (S → E) := by
  infer_instance

/-- The **tail conditional kernel**: a regular conditional distribution of the identity given the
tail σ-algebra `𝓣`. -/
noncomputable def tailKernel : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
  ProbabilityTheory.condExpKernel (mΩ := MeasurableSpace.pi) μ (@tailSigmaAlgebra S E _)

instance : IsMarkovKernel (tailKernel (S := S) (E := E) μ) := by
  simpa [tailKernel] using (by infer_instance : IsMarkovKernel (ProbabilityTheory.condExpKernel (mΩ := MeasurableSpace.pi)
    μ (@tailSigmaAlgebra S E _)))

lemma tailKernel_comp_trim :
    tailKernel (S := S) (E := E) μ ∘ₘ μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))
      = μ := by
  simpa [tailKernel] using
    (ProbabilityTheory.condExpKernel_comp_trim (μ := μ) (m := (@tailSigmaAlgebra S E _))
      (mΩ := MeasurableSpace.pi) (hm := tailSigmaAlgebra_le_pi (S := S) (E := E)))

/-! ## Tail events are {0,1}-valued under the tail kernel (a.e.) -/

omit [Countable S] [StandardBorelSpace E] in
lemma condExp_tail_of_measurableSet (A : Set (S → E))
    (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    MeasureTheory.condExp (@tailSigmaAlgebra S E _) μ (A.indicator fun _ : S → E => (1 : ℝ))
      = A.indicator fun _ : S → E => (1 : ℝ) := by
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  haveI : SigmaFinite (μ.trim hm) := by infer_instance
  have hSM : StronglyMeasurable[@tailSigmaAlgebra S E _] (A.indicator fun _ : S → E => (1 : ℝ)) :=
    (stronglyMeasurable_const.indicator hA)
  have hA_pi : MeasurableSet A := hm _ hA
  have hInt : Integrable (A.indicator fun _ : S → E => (1 : ℝ)) μ := by
    simpa using ((integrable_const (μ := μ) (c := (1 : ℝ))).indicator hA_pi)
  simpa using (MeasureTheory.condExp_of_stronglyMeasurable (μ := μ) (m := (@tailSigmaAlgebra S E _))
    (m₀ := MeasurableSpace.pi) (hm := hm) hSM hInt)

lemma tailKernel_real_eq_indicator_of_measurableSet (A : Set (S → E))
    (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    (fun ω : S → E => (tailKernel (S := S) (E := E) μ ω).real A)
      =ᵐ[μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E))]
        (A.indicator fun _ : S → E => (1 : ℝ)) := by
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  have hA_pi : MeasurableSet A := hm _ hA
  have h1 :
      (fun ω : S → E => (ProbabilityTheory.condExpKernel (mΩ := MeasurableSpace.pi) μ (@tailSigmaAlgebra S E _) ω).real A)
        =ᵐ[μ.trim hm] μ⟦A|(@tailSigmaAlgebra S E _)⟧ :=
    ProbabilityTheory.condExpKernel_ae_eq_trim_condExp (μ := μ) (m := (@tailSigmaAlgebra S E _))
      (mΩ := MeasurableSpace.pi) (hm := hm) (hs := hA_pi)
  have h2 :
      (μ⟦A|(@tailSigmaAlgebra S E _)⟧ : (S → E) → ℝ)
        = (A.indicator fun _ : S → E => (1 : ℝ)) := by
    simpa using
      (condExp_tail_of_measurableSet (S := S) (E := E) (μ := μ) A hA)
  simpa [tailKernel, h2] using h1

/-! ## The law of the tail-conditional measures and a barycenter identity -/

/-- The **law** of the tail-conditional measures: pushforward of `μ.trim (𝓣 ≤ pi)` under the map
`ω ↦ tailKernel μ ω`. -/
noncomputable def tailKernelLaw : Measure (Measure (S → E)) :=
  μ.map (tailKernel (S := S) (E := E) μ)

lemma measurable_tailKernel_pi :
    @Measurable (S → E) (Measure (S → E)) MeasurableSpace.pi Measure.instMeasurableSpace
      (tailKernel (S := S) (E := E) μ) := by
  exact (tailKernel (S := S) (E := E) μ).measurable.mono
    (tailSigmaAlgebra_le_pi (S := S) (E := E)) le_rfl

lemma lintegral_eval_tailKernelLaw (A : Set (S → E)) (hA : MeasurableSet A) :
    (∫⁻ ν : Measure (S → E), ν A ∂(tailKernelLaw (S := S) (E := E) μ))
      = μ A := by
  classical
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  have hκ_pi : Measurable (tailKernel (S := S) (E := E) μ) :=
    measurable_tailKernel_pi (S := S) (E := E) (μ := μ)
  have hmap :
      (∫⁻ ν : Measure (S → E), ν A ∂(tailKernelLaw (S := S) (E := E) μ))
        =
      ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂μ := by
    have h_eval : Measurable (fun ν : Measure (S → E) => ν A) := Measure.measurable_coe hA
    simpa [tailKernelLaw] using
      (MeasureTheory.lintegral_map (μ := μ)
        (f := fun ν : Measure (S → E) => ν A)
        (g := tailKernel (S := S) (E := E) μ) h_eval hκ_pi)
  have htrim :
      (∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂μ)
        =
      ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) := by
    have hmeas_tail :
        Measurable[@tailSigmaAlgebra S E _] (fun ω : S → E => (tailKernel (S := S) (E := E) μ ω) A) := by
      exact (ProbabilityTheory.Kernel.measurable_coe (tailKernel (S := S) (E := E) μ) hA)
    simp [MeasureTheory.lintegral_trim hm hmeas_tail]
  have hdis :
      ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) = μ A := by
    have hκ_tail : Measurable[@tailSigmaAlgebra S E _] (tailKernel (S := S) (E := E) μ) :=
      (tailKernel (S := S) (E := E) μ).measurable
    have hbind :
        (tailKernel (S := S) (E := E) μ ∘ₘ (μ.trim hm)) A
          = ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) := by
      simp [Measure.bind_apply hA hκ_tail.aemeasurable]
    have hcomp : tailKernel (S := S) (E := E) μ ∘ₘ (μ.trim hm) = μ := by
      simpa using tailKernel_comp_trim (S := S) (E := E) (μ := μ)
    simpa [hbind] using congrArg (fun m' : Measure (S → E) => m' A) hcomp
  calc
    (∫⁻ ν : Measure (S → E), ν A ∂(tailKernelLaw (S := S) (E := E) μ))
        = ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂μ := hmap
    _ = ∫⁻ ω : S → E, (tailKernel (S := S) (E := E) μ ω) A ∂(μ.trim hm) := htrim
    _ = μ A := hdis

/-! ## Tail-determinism of the tail kernel (hence tail-triviality of its conditional measures) -/

/-- View the tail kernel as a kernel into the **tail σ-algebra**, by mapping each conditional
measure along `id : (S → E) → (S → E)` from `MeasurableSpace.pi` to `𝓣`. -/
noncomputable def tailKernelTail :
    Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E) :=
  @ProbabilityTheory.Kernel.map (α := (S → E)) (β := (S → E)) (γ := (S → E))
    (@tailSigmaAlgebra S E _) MeasurableSpace.pi (@tailSigmaAlgebra S E _)
    (tailKernel (S := S) (E := E) μ) id

instance : IsMarkovKernel (tailKernelTail (S := S) (E := E) μ) := by
  have hid :
      @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
    measurable_id.mono le_rfl (tailSigmaAlgebra_le_pi (S := S) (E := E))
  simpa [tailKernelTail] using
    (ProbabilityTheory.Kernel.IsMarkovKernel.map (κ := tailKernel (S := S) (E := E) μ) (f := id) hid)

lemma tailKernelTail_apply (ω : S → E) :
    tailKernelTail (S := S) (E := E) μ ω =
      @Measure.map (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _)
        id (tailKernel (S := S) (E := E) μ ω) := by
  have hid :
      @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
    measurable_id.mono le_rfl (tailSigmaAlgebra_le_pi (S := S) (E := E))
  simp [tailKernelTail, ProbabilityTheory.Kernel.map_apply, hid]

lemma tailKernelTail_ae_eq_id
    [@MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) (@tailSigmaAlgebra S E _)] :
    ∀ᵐ ω ∂μ.trim (tailSigmaAlgebra_le_pi (S := S) (E := E)),
      tailKernelTail (S := S) (E := E) μ ω
        = (@ProbabilityTheory.Kernel.id (S → E) (@tailSigmaAlgebra S E _)) ω := by
  classical
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  let μT : Measure[@tailSigmaAlgebra S E _] (S → E) := μ.trim hm
  have hμT : IsFiniteMeasure μT := by infer_instance
  have hcompProd :
      @Measure.compProd (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)
        μT (tailKernelTail (S := S) (E := E) μ)
        =
      @Measure.compProd (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)
        μT
          (ProbabilityTheory.Kernel.id :
            Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)) := by
    let C : Set (Set ((S → E) × (S → E))) :=
      Set.image2 (fun s t => s ×ˢ t)
        ({s : Set (S → E) | MeasurableSet[@tailSigmaAlgebra S E _] s})
        ({t : Set (S → E) | MeasurableSet[@tailSigmaAlgebra S E _] t})
    have hgen :
        (@Prod.instMeasurableSpace (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _))
          = MeasurableSpace.generateFrom C := by
      simpa [C] using
        (show MeasurableSpace.generateFrom C =
              (@Prod.instMeasurableSpace (S → E) (S → E) (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)) from
          (@generateFrom_prod (α := (S → E)) (β := (S → E))
            (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _))).symm
    have hpi : IsPiSystem C := by
      simpa [C] using
        (show IsPiSystem C from
          (@isPiSystem_prod (α := (S → E)) (β := (S → E))
            (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)))
    haveI :
        IsFiniteMeasure
          (μT ⊗ₘ tailKernelTail (S := S) (E := E) μ) := by
      refine ⟨?_⟩
      have h_univ :
          (μT ⊗ₘ tailKernelTail (S := S) (E := E) μ) Set.univ = μT Set.univ := by
        simp
      simp
    refine MeasureTheory.ext_of_generate_finite (m0 := (@Prod.instMeasurableSpace (S → E) (S → E)
        (@tailSigmaAlgebra S E _) (@tailSigmaAlgebra S E _)))
      (μ := (μT ⊗ₘ tailKernelTail (S := S) (E := E) μ))
      (ν := (μT ⊗ₘ
        (ProbabilityTheory.Kernel.id :
          Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E))))
      (C := C) hgen hpi ?_ ?_
    · intro s hsC
      rcases hsC with ⟨A, hA, B, hB, rfl⟩
      have hA' : MeasurableSet[@tailSigmaAlgebra S E _] A := hA
      have hB' : MeasurableSet[@tailSigmaAlgebra S E _] B := hB
      have hLHS :
          (μT ⊗ₘ tailKernelTail (S := S) (E := E) μ) (A ×ˢ B)
            = ∫⁻ ω in A, (tailKernelTail (S := S) (E := E) μ ω) B ∂μT := by
        simp [MeasureTheory.Measure.compProd_apply_prod hA' hB']
      have hRHS :
          (μT ⊗ₘ
            (ProbabilityTheory.Kernel.id :
              Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E))) (A ×ˢ B)
            = ∫⁻ ω in A, (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) ∂μT := by
        have : ∀ ω : S → E,
            (ProbabilityTheory.Kernel.id :
              Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)) ω B =
              B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω := by
          intro ω
          simp [ProbabilityTheory.Kernel.id, ProbabilityTheory.Kernel.deterministic_apply,
            Set.indicator]
          aesop
        simp [MeasureTheory.Measure.compProd_apply_prod hA' hB', this]
      have hB_val :
          (fun ω : S → E => (tailKernel (S := S) (E := E) μ ω) B)
            =ᵐ[μT] (B.indicator (fun _ : S → E => (1 : ℝ≥0∞))) := by
        have hreal :=
          tailKernel_real_eq_indicator_of_measurableSet (S := S) (E := E) (μ := μ) (A := B) hB'
        filter_upwards [hreal] with ω hω
        have hω' :
            ((tailKernel (S := S) (E := E) μ ω) B).toReal =
              (B.indicator (fun _ : S → E => (1 : ℝ)) ω) := by
          simpa [MeasureTheory.measureReal_def] using hω
        have hne_top : (tailKernel (S := S) (E := E) μ ω) B ≠ (⊤ : ℝ≥0∞) := by
          haveI : IsProbabilityMeasure (tailKernel (S := S) (E := E) μ ω) :=
            ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure (κ := tailKernel (S := S) (E := E) μ) ω
          exact measure_ne_top _ _
        have hne_top' :
            (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) ≠ (⊤ : ℝ≥0∞) := by
          by_cases hωB : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hωB]
        have : (tailKernel (S := S) (E := E) μ ω) B =
            (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) := by
          by_cases hωB : ω ∈ B
          · have : (B.indicator (fun _ : S → E => (1 : ℝ)) ω) = 1 := by simp [Set.indicator_of_mem, hωB]
            have : ((tailKernel (S := S) (E := E) μ ω) B).toReal = 1 := by simpa [this] using hω'
            have : (tailKernel (S := S) (E := E) μ ω) B = 1 := by
              exact (ENNReal.toReal_eq_toReal_iff' hne_top (by simp)).1 (by simpa using this)
            simpa [Set.indicator_of_mem, hωB] using this
          · have : (B.indicator (fun _ : S → E => (1 : ℝ)) ω) = 0 := by simp [Set.indicator_of_notMem, hωB]
            have : ((tailKernel (S := S) (E := E) μ ω) B).toReal = 0 := by simpa [this] using hω'
            have : (tailKernel (S := S) (E := E) μ ω) B = 0 := by
              exact (ENNReal.toReal_eq_toReal_iff' hne_top (by simp)).1 (by simpa using this)
            simpa [Set.indicator_of_notMem, hωB] using this
        simp [this]
      have hB_val_restrict :
          (fun ω : S → E => (tailKernelTail (S := S) (E := E) μ ω) B)
            =ᵐ[μT.restrict A] (B.indicator (fun _ : S → E => (1 : ℝ≥0∞))) := by
        have hB_val' :
            (fun ω : S → E => (tailKernelTail (S := S) (E := E) μ ω) B)
              =ᵐ[μT] (B.indicator (fun _ : S → E => (1 : ℝ≥0∞))) := by
          have hid :
              @Measurable (S → E) (S → E) MeasurableSpace.pi (@tailSigmaAlgebra S E _) id :=
            measurable_id.mono le_rfl hm
          filter_upwards [hB_val] with ω hω
          have hmap :
              (tailKernelTail (S := S) (E := E) μ ω) B =
                (tailKernel (S := S) (E := E) μ ω) B := by
            simpa [tailKernelTail, ProbabilityTheory.Kernel.map_apply', hid, hB'] using
              (ProbabilityTheory.Kernel.map_apply'
                (κ := tailKernel (S := S) (E := E) μ)
                (f := (id : (S → E) → (S → E))) hid ω hB')
          simpa [hmap] using hω
        exact MeasureTheory.ae_restrict_of_ae (μ := μT) (s := A) hB_val'
      have hI :
          ∫⁻ ω in A, (tailKernelTail (S := S) (E := E) μ ω) B ∂μT
            = ∫⁻ ω in A, (B.indicator (fun _ : S → E => (1 : ℝ≥0∞)) ω) ∂μT := by
        simp [MeasureTheory.lintegral_congr_ae hB_val_restrict]
      simp [hLHS, hRHS, hI]
    · simp
  haveI : MeasurableSpace.CountableOrCountablyGenerated (S → E) (S → E) :=
    MeasurableSpace.instCountableOrCountablyGeneratedOfCountablyGenerated
  haveI :
      IsFiniteKernel
        (ProbabilityTheory.Kernel.id :
          Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)) := by
    infer_instance
  haveI : MeasurableSpace.CountablyGenerated (S → E) :=
    countablyGenerated_of_standardBorel
  simpa [μT, hm] using
    (ProbabilityTheory.Kernel.ae_eq_of_compProd_eq (μ := μT)
      (κ := tailKernelTail (S := S) (E := E) μ)
      (η := (ProbabilityTheory.Kernel.id :
        Kernel[@tailSigmaAlgebra S E _, @tailSigmaAlgebra S E _] (S → E) (S → E)))
      hcompProd)

end TailKernel

end GibbsMeasure

end MeasureTheory
