import GibbsMeasure.HopfieldFromParamsReal

/-!
## Atomic energy bridge lemmas (real spins)

This file provides the singleton/pair evaluation lemmas for
`GibbsMeasure.Examples.HopfieldFromParamsReal.hopfieldPotentialFromParamsR`.

These lemmas are the deterministic “atoms” used in the full
`interactingHamiltonian = Hopfield energy` proof.
-/

open scoped BigOperators

namespace GibbsMeasure.Examples.HopfieldEnergyBridgeReal

open GibbsMeasure.Examples.HopfieldFromParamsReal

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

lemma hopfieldPotentialFromParamsR_singleton
    (p : Params (HopfieldNetwork ℝ U)) (i : U) (η : U → ℝ) :
    hopfieldPotentialFromParamsR (U := U) p ({i} : Finset U) η
      = θu (U := U) p i * η i := by
  classical
  -- `card {i} = 1`, so we take the singleton branch and the `attach.sum` collapses.
  have hcard1 : ({i} : Finset U).card = 1 := by simp
  let si : {x // x ∈ ({i} : Finset U)} := ⟨i, by simp⟩
  have hatt : ({i} : Finset U).attach = ({si} : Finset {x // x ∈ ({i} : Finset U)}) := by
    ext x
    constructor
    · intro _hx
      have hxval : (x.1 : U) = i := by
        exact (Finset.mem_singleton.1 x.2)
      have : x = si := by
        apply Subtype.ext
        simp [si, hxval]
      simp [this]
    · intro _hx
      simp
  simp [hopfieldPotentialFromParamsR, hcard1, hatt, θu, si]

lemma hopfieldPotentialFromParamsR_pair
    (p : Params (HopfieldNetwork ℝ U)) {i j : U} (hij : i ≠ j) (η : U → ℝ) :
    hopfieldPotentialFromParamsR (U := U) p ({i, j} : Finset U) η
      =
      (- (1 / 2 : ℝ)) * ((p.w i j) * (η i) * (η j) + (p.w j i) * (η j) * (η i)) := by
  classical
  have hcard : ({i, j} : Finset U).card = 2 := by simpa using Finset.card_pair hij
  have hcard1 : ({i, j} : Finset U).card ≠ 1 := by simp [Finset.card_pair hij]
  let si : {x // x ∈ ({i, j} : Finset U)} := ⟨i, by simp⟩
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
    · intro _hx
      simpa using (Finset.mem_attach ({i, j} : Finset U) x)
  have hji : j ≠ i := hij.symm
  have hij' : (si.1 : U) ≠ sj.1 := by simpa [si, sj] using hij
  have hji' : (sj.1 : U) ≠ si.1 := by simpa [si, sj] using hji
  have h_inner_si :
      ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun b =>
        if (b.1 : U) ≠ si.1 then p.w si.1 b.1 * (η si.1) * (η b.1) else 0)
        =
        (p.w i j) * (η i) * (η j) := by
    simp [Finset.sum_pair hsij, hij', hji', si, sj]
  have h_inner_sj :
      ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun b =>
        if (b.1 : U) ≠ sj.1 then p.w sj.1 b.1 * (η sj.1) * (η b.1) else 0)
        =
        (p.w j i) * (η j) * (η i) := by
    simp [Finset.sum_pair hsij, hij', hji', si, sj]
  have h_outer :
      ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun a =>
        ({si, sj} : Finset {x // x ∈ ({i, j} : Finset U)}).sum (fun b =>
          if (b.1 : U) ≠ a.1 then p.w a.1 b.1 * (η a.1) * (η b.1) else 0))
        =
        (p.w i j) * (η i) * (η j) + (p.w j i) * (η j) * (η i) := by
    simp [Finset.sum_pair hsij, h_inner_si, h_inner_sj, si, sj, hij, hij.symm]
  have h_outer' :
      (({i, j} : Finset U).attach.sum fun a =>
        (({i, j} : Finset U).attach.sum fun b =>
          if (b.1 : U) ≠ a.1 then p.w a.1 b.1 * (η a.1) * (η b.1) else 0))
        =
        (p.w i j) * (η i) * (η j) + (p.w j i) * (η j) * (η i) := by
    simpa [hatt] using h_outer
  -- Keep the final normalization step in the same robust “forced simp normal form” style as the Int bridge.
  simp [hopfieldPotentialFromParamsR, hcard, hcard1, h_outer']
  simp_all only [ne_eq, Finset.mem_singleton, not_false_eq_true, Finset.card_insert_of_notMem,
    Finset.card_singleton, Nat.reduceAdd, OfNat.ofNat_ne_one, Subtype.mk.injEq, Finset.attach_insert, ite_not,
    Finset.sum_insert, ↓reduceIte, Finset.sum_singleton, zero_add, add_zero, SetLike.coe_eq_coe, si, sj]

end GibbsMeasure.Examples.HopfieldEnergyBridgeReal
