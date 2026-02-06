import GibbsMeasure.HopfieldFromParamsReal
import GibbsMeasure.HopfieldLocalFlipAtomsReal
import GibbsMeasure.Potential

/-!
## One-site Hamiltonian flip identity (real spins)

This file sums the atomic flip identities from `GibbsMeasure/HopfieldLocalFlipAtomsReal.lean` to
obtain the **full one-site interacting Hamiltonian identity** in volume `{u}` for general
configurations `η : U → ℝ`:

\[
H^{int}_{\{u\}}(\eta[u\mapsto +1]) - H^{int}_{\{u\}}(\eta[u\mapsto -1])
= -2\big(\mathrm{field}(u;\eta) - \theta_u\big),
\]

where `field(u;η) = ∑_{v ≠ u} w_{uv} η v`.

This is the “pure Hamiltonian” bridge theorem (no probability, no DLR).
-/

namespace GibbsMeasure.Examples.HopfieldOneSiteHamiltonianFlipReal

open GibbsMeasure.Examples.HopfieldFromParamsReal
open GibbsMeasure.Examples.HopfieldLocalFlipAtomsReal
open Potential
open scoped BigOperators

variable {U : Type} [DecidableEq U] [Fintype U] [Nonempty U]

noncomputable section

/-! ### Public abbreviations (exported)

These are used by downstream bridge files (probability ratio → logistic → TwoState kernel).
-/

/-- Hopfield Georgii potential from Hopfield parameters (real spins). -/
abbrev Φ (p : Params (HopfieldNetwork ℝ U)) : Potential U ℝ :=
  hopfieldPotentialFromParamsR (U := U) p

instance (p : Params (HopfieldNetwork ℝ U)) : Potential.IsFinitary (Φ (U := U) p) := by
  simpa [Φ] using (inferInstance : Potential.IsFinitary (hopfieldPotentialFromParamsR (U := U) p))

instance (p : Params (HopfieldNetwork ℝ U)) : Potential.IsPotential (Φ (U := U) p) := by
  simpa [Φ] using (inferInstance : Potential.IsPotential (hopfieldPotentialFromParamsR (U := U) p))

/-- The one-site volume `{u}`. -/
abbrev oneSite (u : U) : Finset U := ({u} : Finset U)

private def Su (u : U) : Finset (Finset U) :=
  ({({u} : Finset U)} : Finset (Finset U)) ∪
    (Finset.univ.erase u).image (fun v : U => ({u, v} : Finset U))

/-- Local field sum \(\sum_{v \neq u} w_{uv}\,\eta(v)\) written as a `Finset.erase` sum. -/
abbrev field (p : Params (HopfieldNetwork ℝ U)) (η : U → ℝ) (u : U) : ℝ :=
  ∑ v ∈ Finset.univ.erase u, p.w u v * η v

private lemma diff_zero_of_not_mem_support
    (p : Params (HopfieldNetwork ℝ U)) {Δ : Finset U} (u : U) (η : U → ℝ)
    (hΔ : Δ ∉ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset) :
    Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
      Φ (U := U) p Δ (Function.update η u (-1 : ℝ)) = 0 := by
  classical
  have hmem :
      Δ ∈ (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset ↔ Φ (U := U) p Δ ≠ 0 :=
    (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).mem_toFinset
  have hΦ0 : Φ (U := U) p Δ = 0 := by
    exact (not_ne_iff.1 (by
      intro hne
      exact hΔ (hmem.2 hne)))
  simp [hΦ0]

private lemma filter_support_subset_Su (p : Params (HopfieldNetwork ℝ U)) (u : U) :
    let supp := (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset
    (supp.filter (fun Δ : Finset U => Δ ∩ (oneSite (u := u)) ≠ ∅)) ⊆ Su (U := U) u := by
  classical
  intro supp Δ hΔ
  have hΔ' := Finset.mem_filter.1 hΔ
  have hΔsupp : Δ ∈ supp := hΔ'.1
  -- membership in the finitary support means `Φ Δ ≠ 0` as a function, hence card 1 or 2
  have hmem :
      Δ ∈ supp ↔ Φ (U := U) p Δ ≠ 0 :=
    (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).mem_toFinset
  have hΦne : Φ (U := U) p Δ ≠ 0 := (hmem.1 hΔsupp)
  have hcard : Δ.card = 1 ∨ Δ.card = 2 := by
    by_contra hcard
    have hne1 : Δ.card ≠ 1 := by intro h1; exact hcard (Or.inl h1)
    have hne2 : Δ.card ≠ 2 := by intro h2; exact hcard (Or.inr h2)
    have hzero : Φ (U := U) p Δ = 0 := by
      funext η
      simp [Φ, hopfieldPotentialFromParamsR, hne2, hne1]
    exact hΦne hzero
  -- intersection with `{u}` is nonempty, so `u ∈ Δ`
  have hmeet : Δ ∩ (oneSite (u := u)) ≠ ∅ := hΔ'.2
  have huΔ : u ∈ Δ := by
    have hne : (Δ ∩ oneSite (u := u)).Nonempty :=
      Finset.nonempty_iff_ne_empty.2 hmeet
    rcases hne with ⟨x, hx⟩
    have hxΔ : x ∈ Δ := (Finset.mem_inter.1 hx).1
    have hxU : x ∈ oneSite (u := u) := (Finset.mem_inter.1 hx).2
    have : x = u := by simpa [oneSite] using (Finset.mem_singleton.1 hxU)
    simpa [this] using hxΔ
  cases hcard with
  | inl h1 =>
      rcases Finset.card_eq_one.1 h1 with ⟨x, rfl⟩
      have : u = x := by simpa using huΔ
      have : x = u := this.symm
      subst this
      simp [Su]
  | inr h2 =>
      rcases Finset.card_eq_two.1 h2 with ⟨i, j, hij, rfl⟩
      have hu : u = i ∨ u = j := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using huΔ
      cases hu with
      | inl hui =>
          subst hui
          have hj : j ∈ Finset.univ.erase u := by
            refine Finset.mem_erase.2 ⟨hij.symm, by simp⟩
          refine Finset.mem_union.2 (Or.inr ?_)
          exact Finset.mem_image.2 ⟨j, hj, rfl⟩
      | inr huj =>
          subst huj
          have hi : i ∈ Finset.univ.erase u := by
            refine Finset.mem_erase.2 ⟨hij, by simp⟩
          refine Finset.mem_union.2 (Or.inr ?_)
          exact Finset.mem_image.2 ⟨i, hi, by simp [Finset.pair_comm]⟩

/-- The one-site interacting Hamiltonian flip equals `2*θu - 2*field`. -/
theorem interactingHamiltonian_oneSite_flip
    (p : Params (HopfieldNetwork ℝ U)) (u : U) (η : U → ℝ) :
    interactingHamiltonian (Φ := Φ (U := U) p) (Λ := oneSite (u := u)) (Function.update η u (1 : ℝ))
      -
    interactingHamiltonian (Φ := Φ (U := U) p) (Λ := oneSite (u := u)) (Function.update η u (-1 : ℝ))
      =
      (2 : ℝ) * θu (U := U) p u - (2 : ℝ) * field (U := U) p η u := by
  classical
  -- unfold Hamiltonian as a finite sum over the finitary support filtered by meeting `{u}`
  unfold Potential.interactingHamiltonian
  set supp := (Potential.IsFinitary.finite_support (Φ := Φ (U := U) p)).toFinset with hsupp
  set t := supp.filter (fun Δ : Finset U => Δ ∩ oneSite (u := u) ≠ ∅) with ht
  -- rewrite the difference as a sum of differences
  have hdiff :
      (∑ Δ ∈ t, Φ (U := U) p Δ (Function.update η u (1 : ℝ))) -
        (∑ Δ ∈ t, Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))
        =
      ∑ Δ ∈ t, (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
        Φ (U := U) p Δ (Function.update η u (-1 : ℝ))) := by
    simp [Finset.sum_sub_distrib]
  -- reduce to summing over `Su` by adding zero terms outside `t`
  have ht_sub : t ⊆ Su (U := U) u := by
    have h := filter_support_subset_Su (U := U) (p := p) (u := u)
    -- unfold `t`/`supp` so the goal matches `h`
    simp [t, supp] at *
    exact h
  have hzero :
      ∀ Δ, Δ ∈ Su (U := U) u → Δ ∉ t →
        (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
          Φ (U := U) p Δ (Function.update η u (-1 : ℝ))) = 0 := by
    intro Δ hΔSu hΔnot
    -- if `Δ ∈ Su`, then it meets `{u}`; so `Δ ∉ t` implies `Δ ∉ supp`
    have hinter : Δ ∩ oneSite (u := u) ≠ ∅ := by
      rcases Finset.mem_union.1 hΔSu with h1 | h2
      · -- Δ = {u}
        have : Δ = ({u} : Finset U) := by simpa using (Finset.mem_singleton.1 h1)
        subst this; simp [oneSite]
      · rcases Finset.mem_image.1 h2 with ⟨v, hv, rfl⟩
        simp [oneSite]
    have : Δ ∉ supp := by
      intro hΔsupp
      have : Δ ∈ t := Finset.mem_filter.2 ⟨hΔsupp, hinter⟩
      exact hΔnot this
    exact diff_zero_of_not_mem_support (U := U) (p := p) (u := u) (η := η) (Δ := Δ) (by simpa [supp] using this)
  -- evaluate the sum over `Su` explicitly using the atomic flip lemmas
  have hSu :
      ∑ Δ ∈ Su (U := U) u,
          (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
            Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))
        =
      (2 : ℝ) * θu (U := U) p u - (2 : ℝ) * field (U := U) p η u := by
    -- split singleton `{u}` and pair image; use the atomic lemmas
    set s1 : Finset (Finset U) := ({({u} : Finset U)} : Finset (Finset U)) with hs1
    set s2 : Finset (Finset U) :=
      (Finset.univ.erase u).image (fun v : U => ({u, v} : Finset U)) with hs2
    have hs : Su (U := U) u = s1 ∪ s2 := by simp [Su, s1, s2]
    have hdisj : Disjoint s1 s2 := by
      classical
      refine Finset.disjoint_left.2 ?_
      intro Δ hΔ1 hΔ2
      have hΔeq : Δ = ({u} : Finset U) := by simpa [s1] using (Finset.mem_singleton.1 hΔ1)
      rcases Finset.mem_image.1 hΔ2 with ⟨v, hv, rfl⟩
      have hvne : v ≠ u := (Finset.mem_erase.1 hv).1
      -- `{u,v} = {u}` would force `v = u`
      have : v = u := by
        have : v ∈ ({u} : Finset U) := by
          -- `v` is always in `{u, v}`
          simpa [hΔeq] using (by simp : v ∈ ({u, v} : Finset U))
        simpa using (Finset.mem_singleton.1 this)
      exact hvne this
    -- compute the sum over the union, splitting singleton and pair contributions
    have h1 :
        (∑ Δ ∈ s1,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
          = (2 : ℝ) * θu (U := U) p u := by
      simp [s1, Φ, singleton_flip (U := U) (p := p) (u := u) (η := η)]
    have h2 :
        (∑ Δ ∈ s2,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
          = - (2 : ℝ) * field (U := U) p η u := by
      classical
      -- Reindex the sum over pairs using `Finset.sum_image`.
      let g : U → Finset U := fun v => ({u, v} : Finset U)
      have hg : Set.InjOn g (Finset.univ.erase u) := by
        intro v1 hv1 v2 hv2 hv
        have hv1ne : v1 ≠ u := (Finset.mem_erase.1 hv1).1
        have hv1mem : v1 ∈ g v2 := by
          -- `v1 ∈ g v1`, then rewrite using `hv`
          have : v1 ∈ g v1 := by simp [g]
          simpa [g, hv] using this
        have : v1 = u ∨ v1 = v2 := by
          -- `v1 ∈ {u,v2}` iff `v1=u ∨ v1=v2`
          simpa [g, Finset.mem_insert, Finset.mem_singleton] using hv1mem
        exact (this.resolve_left hv1ne)
      -- rewrite the sum over `s2 = image g (erase u)` as a sum over `v ∈ erase u`
      have hreindex :
          (∑ Δ ∈ s2,
              (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
                Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
            =
          ∑ v ∈ Finset.univ.erase u,
              (Φ (U := U) p (g v) (Function.update η u (1 : ℝ)) -
                Φ (U := U) p (g v) (Function.update η u (-1 : ℝ))) := by
        -- `Finset.sum_image` is the additive version of `Finset.prod_image`
        simpa [s2, g] using (Finset.sum_image (f :=
          fun Δ : Finset U =>
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
          (g := g) (s := (Finset.univ.erase u)) hg)
      -- now apply the atomic `pair_flip` pointwise, then factor `-2`
      rw [hreindex]
      have hpoint :
          (∑ v ∈ Finset.univ.erase u,
              (Φ (U := U) p (g v) (Function.update η u (1 : ℝ)) -
                Φ (U := U) p (g v) (Function.update η u (-1 : ℝ))))
            =
          ∑ v ∈ Finset.univ.erase u, (-(2 : ℝ)) * (p.w u v * η v) := by
        refine Finset.sum_congr rfl ?_
        intro v hv
        have huv : u ≠ v := (Finset.mem_erase.1 hv).1.symm
        -- `pair_flip` is stated for `hopfieldPotentialFromParamsR`; unfold `Φ` and `g`.
        have :=
          pair_flip (U := U) (p := p) (u := u) (v := v) huv (η := η)
        -- rewrite `Φ` and `g`, and massage scalars into the chosen normal form
        simpa [Φ, g, mul_assoc, mul_left_comm, mul_comm] using this
      rw [hpoint]
      -- factor the constant and match `field`
      calc
        (∑ v ∈ Finset.univ.erase u, (-(2 : ℝ)) * (p.w u v * η v))
            =
            (-(2 : ℝ)) * (∑ v ∈ Finset.univ.erase u, p.w u v * η v) := by
              -- `Finset.mul_sum` is `a * ∑ f = ∑ a * f`
              simpa using
                (Finset.mul_sum (s := Finset.univ.erase u) (f := fun v => p.w u v * η v)
                  (a := (-(2 : ℝ)))).symm
        _ = - (2 : ℝ) * field (U := U) p η u := by
              simp [field]
    -- combine `h1` and `h2`
    -- sum over the disjoint union, then substitute `h1`/`h2`
    have hunion :
        (∑ Δ ∈ s1 ∪ s2,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
          =
        (∑ Δ ∈ s1,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
          +
        (∑ Δ ∈ s2,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))) := by
      simp [Finset.sum_union hdisj]
    calc
      (∑ Δ ∈ Su (U := U) u,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
          =
        (∑ Δ ∈ s1 ∪ s2,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))) := by
            simp [hs]
      _ =
        (∑ Δ ∈ s1,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ))))
          +
        (∑ Δ ∈ s2,
            (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
              Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))) := hunion
      _ =
        (2 : ℝ) * θu (U := U) p u + (-(2 : ℝ)) * field (U := U) p η u := by
          simp [h1, h2]
      _ = (2 : ℝ) * θu (U := U) p u - (2 : ℝ) * field (U := U) p η u := by
          simp [sub_eq_add_neg]
  -- now enlarge from `t` to `Su` (extra terms are zero)
  have hsum :
      ∑ Δ ∈ t, (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
        Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))
        =
      ∑ Δ ∈ Su (U := U) u, (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
        Φ (U := U) p Δ (Function.update η u (-1 : ℝ))) := by
    exact (Finset.sum_subset ht_sub hzero)
  -- assemble without `simp` search: rewrite the original LHS to the `t`-sum, then use `hdiff`, `hsum`, `hSu`.
  have hmain :
      (∑ Δ ∈ t, Φ (U := U) p Δ (Function.update η u (1 : ℝ))) -
        (∑ Δ ∈ t, Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))
        =
      (2 : ℝ) * θu (U := U) p u - (2 : ℝ) * field (U := U) p η u := by
    calc
      (∑ Δ ∈ t, Φ (U := U) p Δ (Function.update η u (1 : ℝ))) -
          (∑ Δ ∈ t, Φ (U := U) p Δ (Function.update η u (-1 : ℝ)))
          =
        ∑ Δ ∈ t, (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
          Φ (U := U) p Δ (Function.update η u (-1 : ℝ))) := hdiff
      _ =
        ∑ Δ ∈ Su (U := U) u,
          (Φ (U := U) p Δ (Function.update η u (1 : ℝ)) -
            Φ (U := U) p Δ (Function.update η u (-1 : ℝ))) := by
          simpa using hsum
      _ = (2 : ℝ) * θu (U := U) p u - (2 : ℝ) * field (U := U) p η u := hSu
  -- and finally, `t` was defined as the filter used by `interactingHamiltonian`
  simpa [supp, hsupp, t, ht] using hmain

end

end GibbsMeasure.Examples.HopfieldOneSiteHamiltonianFlipReal
