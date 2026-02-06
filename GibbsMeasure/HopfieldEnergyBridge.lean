import GibbsMeasure.HopfieldFromParams
import Mathlib.Data.Finset.Sym

/-!
## Hopfield energy bridge (Talagrand/Georgii alignment lemmas)

This file proves the **atomic evaluation lemmas** for the Hopfield potential induced by
Hopfield parameters (`GibbsMeasure.Examples.HopfieldFromParams.hopfieldPotentialFromParams`).

These are the building blocks for the main bridge lemma:

`NeuralNetwork.State.E = Potential.interactingHamiltonian` (finite volume / univ).

We proceed in the “principled” order:
1. compute singleton contributions (threshold term),
2. compute pair contributions (weight term, with the correct `-1/2` convention),
3. later: sum pair supports canonically via `Finset.sym2` (unordered pairs) to avoid double counting.
-/

open scoped BigOperators

namespace GibbsMeasure.Examples.HopfieldEnergyBridge

open GibbsMeasure.Examples.HopfieldFromParams

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

/-! ### Singleton support -/

lemma hopfieldPotentialFromParams_singleton
    (p : Params (HopfieldNetwork ℝ U)) (i : U) (η : U → Int) :
    hopfieldPotentialFromParams (U := U) p ({i} : Finset U) η
      = θu (U := U) p i * (η i : ℝ) := by
  classical
  -- `card {i} = 1`, so we take the singleton branch and the `attach.sum` collapses.
  have hcard2 : ({i} : Finset U).card ≠ 2 := by simp
  have hcard1 : ({i} : Finset U).card = 1 := by simp
  -- Identify the attached finset explicitly.
  let si : {x // x ∈ ({i} : Finset U)} := ⟨i, by simp⟩
  have hatt : ({i} : Finset U).attach = ({si} : Finset {x // x ∈ ({i} : Finset U)}) := by
    ext x
    constructor
    · intro _hx
      -- any element of a singleton-subtype has value `i`
      have hxval : (x.1 : U) = i := by
        exact (Finset.mem_singleton.1 x.2)
      -- hence `x = si`
      have : x = si := by
        apply Subtype.ext
        simp [si, hxval]
      simp [this]
    · intro hx
      -- reverse direction: membership in `{si}` is trivial
      -- `x ∈ ({i}.attach)` is always true (it is the finset of all elements of the subtype).
      simp
  simp [hopfieldPotentialFromParams, hcard1, hatt, θu, si]

/-! ### Pair support -/

lemma hopfieldPotentialFromParams_pair
    (p : Params (HopfieldNetwork ℝ U)) {i j : U} (hij : i ≠ j) (η : U → Int) :
    hopfieldPotentialFromParams (U := U) p ({i, j} : Finset U) η
      =
      (- (1 / 2 : ℝ)) *
        ((p.w i j) * (η i : ℝ) * (η j : ℝ) + (p.w j i) * (η j : ℝ) * (η i : ℝ)) := by
  classical
  -- `card {i,j} = 2`, so we take the pair branch.
  have hcard : ({i, j} : Finset U).card = 2 := by simpa using Finset.card_pair hij
  have hcard1 : ({i, j} : Finset U).card ≠ 1 := by
    simp [Finset.card_pair hij]
  -- Identify the attached finset explicitly.
  let si : {x // x ∈ ({i, j} : Finset U)} := ⟨i, by simp⟩
  -- Note: membership `j ∈ {i,j}` is definitional; we do not inject `hij` into the proof term,
  -- to keep later simplifications deterministic (no spurious case splits).
  let sj : {x // x ∈ ({i, j} : Finset U)} := ⟨j, by simp⟩
  have hsij : si ≠ sj := by
    intro h
    have : (si.1 : U) = sj.1 := congrArg Subtype.val h
    exact hij this
  have hatt :
      ({i, j} : Finset U).attach =
        ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}) := by
    ext x
    constructor
    · intro _hx
      have hx' : (x.1 : U) = i ∨ (x.1 : U) = j := by
        have := (Finset.mem_insert.1 x.2)
        cases this with
        | inl h => exact Or.inl h
        | inr hjmem => exact Or.inr (Finset.mem_singleton.1 hjmem)
      cases hx' with
      | inl hxi =>
          have : x = si := by
            apply Subtype.ext
            simpa [si] using hxi
          simp [this]
      | inr hxj =>
          have : x = sj := by
            apply Subtype.ext
            simpa [sj] using hxj
          simp [this]
    · intro hx
      -- membership in the attach is automatic once we are in `{si,sj}`
      simpa using (Finset.mem_attach ({i, j} : Finset U) x)
  -- Expand the double sum over the two attached points.
  -- We keep the algebra explicit so the normal form matches the statement.
  have hji : j ≠ i := hij.symm
  have hij' : (si.1 : U) ≠ sj.1 := by simpa [si, sj] using hij
  have hji' : (sj.1 : U) ≠ si.1 := by simpa [si, sj] using hji
  -- Rewrite `attach` to `{si,sj}`, then evaluate the nested sums using `Finset.sum_pair`.
  have h_inner_si :
      ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun b =>
        if (b.1 : U) ≠ si.1 then p.w si.1 b.1 * (η si.1 : ℝ) * (η b.1 : ℝ) else 0)
        =
        (p.w i j) * (η i : ℝ) * (η j : ℝ) := by
    -- `sum_pair` expands the 2-element sum; diagonal term is `0`, off-diagonal uses `hij`.
    simp [Finset.sum_pair hsij, hij', hji', si, sj]
  have h_inner_sj :
      ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun b =>
        if (b.1 : U) ≠ sj.1 then p.w sj.1 b.1 * (η sj.1 : ℝ) * (η b.1 : ℝ) else 0)
        =
        (p.w j i) * (η j : ℝ) * (η i : ℝ) := by
    simp [Finset.sum_pair hsij, hij', hji', si, sj]
  have h_outer :
      ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun a =>
        ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun b =>
          if (b.1 : U) ≠ a.1 then p.w a.1 b.1 * (η a.1 : ℝ) * (η b.1 : ℝ) else 0))
        =
        (p.w i j) * (η i : ℝ) * (η j : ℝ) + (p.w j i) * (η j : ℝ) * (η i : ℝ) := by
    -- outer `sum_pair` over `a = si,sj`, then use the inner evaluations.
    -- the remaining `if i=j then ...` branches are killed by `hij` / `hij.symm`.
    simp [Finset.sum_pair hsij, si, sj, hij, hij.symm, hij', hji', h_inner_si, h_inner_sj]
  -- Transport `h_outer` back to the actual `Δ.attach.sum` appearing in the potential.
  have h_outer' :
      (({i, j} : Finset U).attach.sum fun a =>
        (({i, j} : Finset U).attach.sum fun b =>
          if (b.1 : U) ≠ a.1 then p.w a.1 b.1 * (η a.1 : ℝ) * (η b.1 : ℝ) else 0))
        =
        (p.w i j) * (η i : ℝ) * (η j : ℝ) + (p.w j i) * (η j : ℝ) * (η i : ℝ) := by
    simpa [hatt] using h_outer
  simp [hopfieldPotentialFromParams, hcard, hcard1, h_outer']; simp_all only [ne_eq, Finset.mem_singleton,
    not_false_eq_true, Finset.card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd, OfNat.ofNat_ne_one,
    Subtype.mk.injEq, Finset.attach_insert, ite_not, Finset.sum_insert, ↓reduceIte, Finset.sum_singleton, zero_add,
    add_zero, SetLike.coe_eq_coe, si, sj]

end GibbsMeasure.Examples.HopfieldEnergyBridge
