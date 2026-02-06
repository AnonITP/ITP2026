import GibbsMeasure.Potential
import GibbsMeasure.HopfieldFromParamsReal
import GibbsMeasure.HopfieldEnergyBridgeReal

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
## Hopfield energy = Georgii interacting Hamiltonian (real spins, volume `univ`)

This file proves the finite-volume, mean-field Hamiltonian identity for the Hopfield model:

For a finite index set `U`, Hopfield parameters `p`, and a configuration `η : U → ℝ`,
the Georgii interacting Hamiltonian in volume `Λ = univ` for the params-induced real-spin potential
`hopfieldPotentialFromParamsR p` equals the “Hopfield energy functional”

`E(p, η) = Ew(p, η) + Eθ(p, η)`

where
- `Eθ(p, η) = ∑ u, θu p u * η u`,
- `Ew(p, η) = -1/2 * ∑ u, ∑ v ≠ u, p.w u v * η u * η v`.

We introduce a (noncomputable) linear order on `U` *only* to index each unordered pair `{i,j}` once
via `i < j` in the proof. This is a proof device; the model is choice-free.
-/

open scoped BigOperators

namespace GibbsMeasure.Examples.HopfieldEnergyEqualityReal

open Potential
open GibbsMeasure.Examples.HopfieldFromParamsReal
open GibbsMeasure.Examples.HopfieldEnergyBridgeReal
open scoped BigOperators
open ENNReal MeasureTheory

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

-- Proof-only linear order on a finite type, used for canonical indexing (`i<j`).
local instance : LinearOrder U :=
  LinearOrder.lift' (Fintype.equivFin U) (Fintype.equivFin U).injective

abbrev Φ (p : Params (HopfieldNetwork ℝ U)) : Potential U ℝ :=
  hopfieldPotentialFromParamsR (U := U) p

abbrev Eθ (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) : ℝ :=
  ∑ u : U, θu (U := U) p u * η u

abbrev singletons : Finset (Finset U) :=
  (Finset.univ : Finset U).image (fun i : U => ({i} : Finset U))

abbrev pairsLT : Finset (Finset U) :=
  ((Finset.univ : Finset U).offDiag.filter (fun ij : U × U => ij.1 < ij.2)).image
    (fun ij : U × U => ({ij.1, ij.2} : Finset U))

abbrev bigSupport : Finset (Finset U) :=
  singletons (U := U) ∪ pairsLT (U := U)

abbrev Ew (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) : ℝ :=
  ∑ Δ ∈ pairsLT (U := U), Φ (U := U) p Δ η

abbrev E (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) : ℝ :=
  Ew (U := U) p η + Eθ (U := U) p η

lemma disjoint_singletons_pairsLT :
    Disjoint (singletons (U := U)) (pairsLT (U := U)) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro Δ hΔ1 hΔ2
  rcases Finset.mem_image.1 hΔ1 with ⟨i, _, rfl⟩
  rcases Finset.mem_image.1 hΔ2 with ⟨ij, hij, hijEq⟩
  have hijne : ij.1 ≠ ij.2 := by
    have : ij ∈ (Finset.univ : Finset U).offDiag := (Finset.mem_filter.1 hij).1
    exact (Finset.mem_offDiag.1 this).2.2
  -- card 1 vs card 2, using the equality forced by membership in both images
  have hcardEq : ({ij.1, ij.2} : Finset U).card = ({i} : Finset U).card :=
    congrArg Finset.card hijEq
  have : (2 : ℕ) = 1 := by
    simpa [Finset.card_singleton, Finset.card_pair hijne] using hcardEq
  exact (Nat.succ_ne_self 1) this

lemma mem_bigSupport_of_ne_zero
    (p : Params (HopfieldNetwork ℝ U)) {Δ : Finset U}
    (hΔ : Φ (U := U) p Δ ≠ 0) :
    Δ ∈ bigSupport (U := U) := by
  classical
  -- Only card 1 or 2 can give a nonzero function.
  have hcard : Δ.card = 1 ∨ Δ.card = 2 := by
    by_contra hcard
    have hne1 : Δ.card ≠ 1 := by intro h1; exact hcard (Or.inl h1)
    have hne2 : Δ.card ≠ 2 := by intro h2; exact hcard (Or.inr h2)
    have : Φ (U := U) p Δ = 0 := by
      funext x
      simp [Φ, hopfieldPotentialFromParamsR, hne2, hne1]
    exact hΔ this
  cases hcard with
  | inl h1 =>
      rcases Finset.card_eq_one.1 h1 with ⟨i, rfl⟩
      have : ({i} : Finset U) ∈ singletons (U := U) := by
        refine Finset.mem_image.2 ?_
        exact ⟨i, by simp [singletons], rfl⟩
      simp [bigSupport, this]
  | inr h2 =>
      rcases Finset.card_eq_two.1 h2 with ⟨i, j, hij, rfl⟩
      -- pick the canonical order (`i<j` or `j<i`)
      cases lt_or_gt_of_ne hij with
      | inl hijlt =>
          have hijmem : (i, j) ∈ (Finset.univ : Finset U).offDiag.filter (fun ij : U × U => ij.1 < ij.2) := by
            refine Finset.mem_filter.2 ?_
            refine ⟨?_, hijlt⟩
            refine Finset.mem_offDiag.2 ?_
            simp [hij]
          have : ({i, j} : Finset U) ∈ pairsLT (U := U) := by
            refine Finset.mem_image.2 ?_
            exact ⟨(i, j), hijmem, rfl⟩
          simp [bigSupport, this]
      | inr hjilt =>
          have hijmem : (j, i) ∈ (Finset.univ : Finset U).offDiag.filter (fun ij : U × U => ij.1 < ij.2) := by
            refine Finset.mem_filter.2 ?_
            refine ⟨?_, hjilt⟩
            refine Finset.mem_offDiag.2 ?_
            simp [hij.symm]
          have : ({j, i} : Finset U) ∈ pairsLT (U := U) := by
            refine Finset.mem_image.2 ?_
            exact ⟨(j, i), hijmem, rfl⟩
          have : ({i, j} : Finset U) ∈ pairsLT (U := U) := by
            simpa [Finset.pair_comm] using this
          simp [bigSupport, this]

lemma supp_subset_bigSupport
    (p : Params (HopfieldNetwork ℝ U)) :
    ((Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset)
      ⊆ bigSupport (U := U) := by
  classical
  intro Δ hΔ
  have hmem :
      Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset
        ↔ Φ (U := U) p Δ ≠ 0 :=
    (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).mem_toFinset
  exact mem_bigSupport_of_ne_zero (U := U) p (hmem.1 hΔ)

lemma interactingHamiltonian_univ_eq_sum_support
    (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) :
    interactingHamiltonian (Φ := Φ (U := U) p) (Λ := (Finset.univ : Finset U)) η
      =
      ∑ Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset, Φ (U := U) p Δ η := by
  classical
  -- In `Λ = univ`, the filter condition is `Δ ≠ ∅`; and `∅` is not in the finitary support
  -- because `Φ ∅ = 0` by definition (support = `{Δ | Φ Δ ≠ 0}`).
  unfold Potential.interactingHamiltonian
  classical
  set supp :=
      (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset with hsupp
  -- show the `Λ`-filter is identically true on `supp`
  have hne_empty : ∀ {Δ : Finset U}, Δ ∈ supp → Δ ≠ ∅ := by
    intro Δ hΔ
    have hmem :
        Δ ∈ supp ↔ Φ (U := U) p Δ ≠ 0 := by
      simpa [hsupp] using
        (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).mem_toFinset
    have hΦ : Φ (U := U) p Δ ≠ 0 := (hmem.1 hΔ)
    have hbig : Δ ∈ bigSupport (U := U) := mem_bigSupport_of_ne_zero (U := U) p hΦ
    rcases Finset.mem_union.1 hbig with hsing | hpair
    · rcases Finset.mem_image.1 hsing with ⟨i, _, rfl⟩
      simp
    · rcases Finset.mem_image.1 hpair with ⟨ij, hij, rfl⟩
      simp
  have hfilter : supp.filter (fun Δ : Finset U => Δ ∩ (Finset.univ : Finset U) ≠ ∅) = supp := by
    ext Δ
    by_cases hΔ : Δ ∈ supp
    · have hΔne : ¬ Δ = ∅ := by
        exact hne_empty (Δ := Δ) hΔ
      -- the filter predicate is `Δ ≠ ∅` once we rewrite `Δ ∩ univ = Δ`
      simp [hΔ, Finset.inter_univ, hΔne]
    · simp [hΔ]
  -- finish
  -- rewrite the RHS sum to use `supp`, then use `hfilter`.
  change
      Finset.sum (supp.filter (fun Δ : Finset U => Δ ∩ (Finset.univ : Finset U) ≠ ∅))
        (fun Δ : Finset U => Φ (U := U) p Δ η)
        =
      Finset.sum ((Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset)
        (fun Δ : Finset U => Φ (U := U) p Δ η)
  -- replace the RHS finset with `supp`
  rw [← hsupp]
  -- drop the filter
  rw [hfilter]

lemma sum_support_eq_sum_bigSupport
    (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) :
    (∑ Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset, Φ (U := U) p Δ η)
      =
      ∑ Δ ∈ bigSupport (U := U), Φ (U := U) p Δ η := by
  classical
  have hs : (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset ⊆ bigSupport (U := U) :=
    supp_subset_bigSupport (U := U) p
  -- Outside the true support, the potential is the zero function, hence evaluates to `0`.
  have hzero :
      ∀ Δ, Δ ∈ bigSupport (U := U) →
        Δ ∉ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset →
          Φ (U := U) p Δ η = 0 := by
    intro Δ _hΔbig hΔnot
    have hmem :
        Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset
          ↔ Φ (U := U) p Δ ≠ 0 :=
      (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).mem_toFinset
    have : ¬ (Φ (U := U) p Δ ≠ 0) := by
      intro hne
      exact hΔnot (hmem.2 hne)
    have hΦ0 : Φ (U := U) p Δ = 0 := (not_ne_iff.1 this)
    simp [hΦ0]
  -- `sum_subset` gives equality of sums when we enlarge by zeros.
  exact (Finset.sum_subset hs hzero)

lemma sum_singletons
    (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) :
    (∑ Δ ∈ singletons (U := U), Φ (U := U) p Δ η)
      = Eθ (U := U) p η := by
  classical
  have hinj : Function.Injective (fun u : U => ({u} : Finset U)) := by
    intro a b hab
    have : a ∈ ({b} : Finset U) := by
      simpa [hab] using (by simp : a ∈ ({a} : Finset U))
    simp at this
    simpa using this
  -- Reindex via `u` and use the singleton atom lemma.
  simp [singletons, Φ, Eθ, Finset.sum_image, hinj, hopfieldPotentialFromParamsR_singleton, θu]

lemma sum_pairsLT
    (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) :
    (∑ Δ ∈ pairsLT (U := U), Φ (U := U) p Δ η)
      = Ew (U := U) p η := by
  simp [Ew]

theorem interactingHamiltonian_univ_eq_energy
    (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) :
    interactingHamiltonian (Φ := Φ (U := U) p) (Λ := (Finset.univ : Finset U)) η
      = E (U := U) p η := by
  classical
  -- Step 1: remove the `Λ`-filter (support terms are only singletons/pairs, hence nonempty).
  have hH :
      interactingHamiltonian (Φ := Φ (U := U) p) (Λ := (Finset.univ : Finset U)) η
        =
        ∑ Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset, Φ (U := U) p Δ η := by
    simpa using interactingHamiltonian_univ_eq_sum_support (U := U) p η
  -- Step 2: enlarge the sum to the explicit big support (singletons ∪ pairs), since all other terms are zero.
  have hsum :
      (∑ Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset, Φ (U := U) p Δ η)
        =
      ∑ Δ ∈ bigSupport (U := U), Φ (U := U) p Δ η := by
    simpa using sum_support_eq_sum_bigSupport (U := U) p η
  -- Step 3: split into singleton + pair contributions and evaluate each piece.
  have hsplit :
      (∑ Δ ∈ bigSupport (U := U), Φ (U := U) p Δ η)
        =
      (∑ Δ ∈ singletons (U := U), Φ (U := U) p Δ η) +
      (∑ Δ ∈ pairsLT (U := U), Φ (U := U) p Δ η) := by
    -- disjoint union
    have hd : Disjoint (singletons (U := U)) (pairsLT (U := U)) := disjoint_singletons_pairsLT (U := U)
    simp [bigSupport, Finset.sum_union hd]
  -- Combine.
  calc
    interactingHamiltonian (Φ := Φ (U := U) p) (Λ := (Finset.univ : Finset U)) η
        = ∑ Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset, Φ (U := U) p Δ η := hH
    _ = ∑ Δ ∈ bigSupport (U := U), Φ (U := U) p Δ η := hsum
    _ = (∑ Δ ∈ singletons (U := U), Φ (U := U) p Δ η) +
          (∑ Δ ∈ pairsLT (U := U), Φ (U := U) p Δ η) := hsplit
    _ = Eθ (U := U) p η + Ew (U := U) p η := by
          simp [sum_singletons (U := U) p η, sum_pairsLT (U := U) p η]
    _ = Ew (U := U) p η + Eθ (U := U) p η := by
          ac_rfl
    _ = E (U := U) p η := by simp [E]

end

end GibbsMeasure.Examples.HopfieldEnergyEqualityReal

namespace GibbsMeasure.Examples.HopfieldEnergyEqualityReal

open Potential
open ENNReal MeasureTheory
open scoped BigOperators

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

lemma boltzmannWeight_univ_eq_exp_energy
    (p : Params (HopfieldNetwork ℝ U)) (β : ℝ) (η : U → ℝ) :
    Potential.boltzmannWeight (Φ := Φ (U := U) p) β (Finset.univ : Finset U) η
      =
      ENNReal.ofReal (Real.exp (-β * E (U := U) p η)) := by
  -- By definition, `boltzmannWeight = ofReal (exp (-β * H))`, and `H = E` by the bridge theorem.
  simp [Potential.boltzmannWeight, interactingHamiltonian_univ_eq_energy (U := U) (p := p) (η := η), Φ, E]

end GibbsMeasure.Examples.HopfieldEnergyEqualityReal
