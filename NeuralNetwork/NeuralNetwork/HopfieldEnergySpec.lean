import NeuralNetwork.NeuralNetwork.Core
import NeuralNetwork.NeuralNetwork.TwoState

/-!
# Hopfield energy specification for TwoState Gibbs updates

This file provides a principled bridge:

`HopfieldNetwork R U` (binary spins in `{±1}` with symmetric weights)
→ `TwoStateNeuralNetwork` instance
→ `TwoState.EnergySpec'`:
   - energy `E` is the Hopfield energy from `NeuralNetwork/NeuralNetwork/Core.lean`
   - local field is `net - θ`
   - flip-energy relation is proved *exactly* (no orthogonality assumptions):
     \[
       E(updPos) - E(updNeg) = -2 \cdot (localField).
     \]

With this, you can use:
- `TwoState.gibbsUpdate` (one-site Gibbs / Glauber step),
- `HopfieldBoltzmannR` canonical ensemble + Markov kernels,
- `FastTwoStateGibbs` computable enclosures once a `FastEnergyAtSite` is provided.
-/

open scoped BigOperators

namespace NeuralNetwork

open Matrix Finset
open NeuralNetwork.State
open TwoState

universe uR uU

variable {R : Type uR} {U : Type uU}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [Fintype U] [DecidableEq U] [Nonempty U]

-- A TwoState instance for the Hopfield network: σ = R, σ_pos = 1, σ_neg = -1, m = id.
instance instTwoStateHopfield :
    TwoStateNeuralNetwork (HopfieldNetwork R U) where
  σ_pos := (1 : R)
  σ_neg := (-1 : R)
  h_pos_ne_neg := by
    have : (-1 : R) < 1 := by
      have hneg : (-1 : R) < 0 := by simp
      exact hneg.trans (show (0 : R) < 1 from zero_lt_one)
    exact (ne_of_lt this).symm
  θ0 := fun _ => TwoState.fin0
  h_fact_pos := by
    intro u σcur net θ hle
    -- `fact` for HopfieldNetwork is `if θ.get fin0 ≤ net then 1 else -1`.
    change (if θ.get TwoState.fin0 ≤ net then (1 : R) else -1) = (1 : R)
    simp [HopfieldNetwork, HNfact, hle]
  h_fact_neg := by
    intro u σcur net θ hlt
    have : ¬ (θ.get TwoState.fin0) ≤ net := not_le.mpr hlt
    change (if θ.get TwoState.fin0 ≤ net then (1 : R) else -1) = (-1 : R)
    simp [HopfieldNetwork, HNfact, this]
  h_pact_pos := by
    -- pact is `a = 1 ∨ a = -1`
    simp [HopfieldNetwork]
  h_pact_neg := by
    simp [HopfieldNetwork]
  m_order := by
    have hneg : (-1 : R) < 0 := by simp
    exact hneg.trans (show (0 : R) < 1 from zero_lt_one)

namespace HopfieldEnergySpec

-- Lightweight simp-lemmas so we never need to unfold the full `HopfieldNetwork` record repeatedly.
@[simp] lemma hopfield_fout (u : U) (a : R) : (HopfieldNetwork R U).fout u a = a := by
  rfl

@[simp] lemma hopfield_fnet (u : U) (row : U → R) (pred : U → R) (x : Vector R ((HopfieldNetwork R U).κ1 u)) :
    (HopfieldNetwork R U).fnet u row pred x = HNfnet u row pred := by
  rfl

-- Local field used by the TwoState API: `net - θ`.
def localField (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) : R :=
  (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := HopfieldNetwork R U) u)

@[simp] lemma localField_spec (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    localField (R := R) (U := U) p s u =
      (s.net p u) - (p.θ u).get (TwoStateNeuralNetwork.θ0 (NN := HopfieldNetwork R U) u) := by
  rfl

-- Energy as already defined in `NeuralNetwork/NeuralNetwork/Core.lean`.
def E (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) : R :=
  s.E (wθ := p)

-- Forced-updated states at a site (TwoState API).
abbrev sPos (s : (HopfieldNetwork R U).State) (u : U) : (HopfieldNetwork R U).State :=
  TwoState.updPos (R := R) (U := U) (σ := R) (NN := HopfieldNetwork R U) s u

abbrev sNeg (s : (HopfieldNetwork R U).State) (u : U) : (HopfieldNetwork R U).State :=
  TwoState.updNeg (R := R) (U := U) (σ := R) (NN := HopfieldNetwork R U) s u

/-!
## Small lemmas used by `flip_energy_relation_R`

We keep the proof modular:
- pointwise facts about `updPos/updNeg`,
- rewriting `net` and `localField` into the classical Hopfield “field - θ” form,
- separate `Eθ` and `Ew` difference computations.
-/

-- Abbreviations for the scalar threshold at a site and the usual (filtered) local field sum.
@[inline] def θu (p : Params (HopfieldNetwork R U)) (u : U) : R := (p.θ u).get TwoState.fin0

@[inline] def field (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) : R :=
  ∑ v ∈ ({v : U | v ≠ u} : Finset U), p.w u v * s.act v

@[simp] lemma θu_eq_get_fin0 (p : Params (HopfieldNetwork R U)) (u : U) :
    θu p u = (p.θ u).get TwoState.fin0 := rfl

@[simp] lemma θ0_eq_fin0 (u : U) :
    TwoStateNeuralNetwork.θ0 (NN := HopfieldNetwork R U) u = TwoState.fin0 := rfl

@[simp] lemma sPos_act_self (s : (HopfieldNetwork R U).State) (u : U) :
    (sPos s u).act u = (1 : R) := by
  simp [sPos, TwoState.updPos, instTwoStateHopfield]

@[simp] lemma sNeg_act_self (s : (HopfieldNetwork R U).State) (u : U) :
    (sNeg s u).act u = (-1 : R) := by
  simp [sNeg, TwoState.updNeg, instTwoStateHopfield]

@[simp] lemma sPos_act_of_ne (s : (HopfieldNetwork R U).State) {u v : U} (hv : v ≠ u) :
    (sPos s u).act v = s.act v := by
  simp [sPos, TwoState.updPos, Function.update, hv]

@[simp] lemma sNeg_act_of_ne (s : (HopfieldNetwork R U).State) {u v : U} (hv : v ≠ u) :
    (sNeg s u).act v = s.act v := by
  simp [sNeg, TwoState.updNeg, Function.update, hv]

lemma net_eq_field (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    s.net p u = field p s u := by
  -- `net u = HNfnet u (p.w u) (fun v => out v)` and `out v = act v` since `fout = id`.
  dsimp [NeuralNetwork.State.net, field]
  simp [NeuralNetwork.State.out, hopfield_fnet, hopfield_fout, HNfnet]

lemma localField_eq_field_sub_θu (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    localField (R := R) (U := U) p s u =
      field p s u - θu p u := by
  simp [localField, net_eq_field (p := p) (s := s) (u := u), θu, θ0_eq_fin0 (u := u), sub_eq_add_neg]

lemma w_symm (p : Params (HopfieldNetwork R U)) (i j : U) : p.w i j = p.w j i := by
  -- `p.hw' : p.w.transpose = p.w`
  have h := congrArg (fun M : Matrix U U R => M i j) p.hw'
  -- `transpose i j = M j i`
  simpa [Matrix.transpose] using h.symm

/-! ### Eθ difference -/

lemma Eθ_diff_sPos_sNeg (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    (NeuralNetwork.State.Eθ (s := (sPos s u)) (wθ := p)) -
      (NeuralNetwork.State.Eθ (s := (sNeg s u)) (wθ := p))
      = (2 : R) * θu p u := by
  classical
  -- Split sums at `u` and cancel off-site contributions.
  let S : Finset U := Finset.univ
  have hsplit (t : (HopfieldNetwork R U).State) :
      (∑ x : U, θ' (p.θ x) * t.act x) =
        θ' (p.θ u) * t.act u + ∑ x ∈ (S.erase u), θ' (p.θ x) * t.act x := by
    simpa [S] using
      (Finset.sum_erase_add (s := (Finset.univ : Finset U)) (a := u)
        (f := fun x => θ' (p.θ x) * t.act x) (by simp)).symm
  have hrest :
      (∑ x ∈ (S.erase u), θ' (p.θ x) * (sPos s u).act x) =
      (∑ x ∈ (S.erase u), θ' (p.θ x) * (sNeg s u).act x) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hx' : x ≠ u := (Finset.mem_erase.mp hx).1
    simp [sPos_act_of_ne (s := s) hx', sNeg_act_of_ne (s := s) hx']
  -- Now compute: unfold `Eθ`, rewrite both sums using `hsplit`, cancel the rest via `hrest`.
  -- (We avoid `simp`/`ring_nf` on expressions containing `Wact`/`Eθ` to prevent heartbeats.)
  dsimp [NeuralNetwork.State.Eθ]
  -- apply the split identities to both sums
  rw [hsplit (t := (sPos s u)), hsplit (t := (sNeg s u))]
  -- cancel the off-site part
  -- after rewriting, both expressions share the same tail sum
  -- use `hrest` to replace the tail sum from `sPos` with the one from `sNeg`.
  rw [hrest]
  -- now the tails are identical; cancel them using `(a + r) - (b + r) = a - b`
  have hcancel :
      (θ' (p.θ u) * (sPos s u).act u + ∑ x ∈ (S.erase u), θ' (p.θ x) * (sNeg s u).act x)
        -
        (θ' (p.θ u) * (sNeg s u).act u + ∑ x ∈ (S.erase u), θ' (p.θ x) * (sNeg s u).act x)
        =
      (θ' (p.θ u) * (sPos s u).act u) - (θ' (p.θ u) * (sNeg s u).act u) := by
    simpa [add_sub_add_right_eq_sub]
  -- replace the LHS difference with the simplified one
  rw [hcancel]
  rw [sPos_act_self (s := s) u, sNeg_act_self (s := s) u]
  -- Replace `θ'` by the same coordinate as `θu`, then finish by ring algebra.
  change (θ' (p.θ u) * (1 : R) - θ' (p.θ u) * (-1 : R)) = (2 : R) * ((p.θ u).get TwoState.fin0)
  simp [θ', TwoState.fin0]
  ring_nf

/-! ### Ew difference -/

-- The “rest” term in `Ew_update_formula_split` is insensitive to forcing the spin at `u`.
lemma Ew_rest_eq_sPos_sNeg (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    (-1 / 2 : R) *
        (∑ v1 : U, ∑ v2 ∈ {v2 : U | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u},
            (sPos s u).Wact (wθ := p) v1 v2)
      =
    (-1 / 2 : R) *
        (∑ v1 : U, ∑ v2 ∈ {v2 : U | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u},
            (sNeg s u).Wact (wθ := p) v1 v2) := by
  classical
  refine congrArg (fun z => (-1 / 2 : R) * z) ?_
  refine (Fintype.sum_congr
    (f := fun v1 : U =>
      ∑ v2 ∈ {v2 : U | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u},
        (sPos s u).Wact (wθ := p) v1 v2)
    (g := fun v1 : U =>
      ∑ v2 ∈ {v2 : U | (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u},
        (sNeg s u).Wact (wθ := p) v1 v2)
    (fun v1 => ?_))
  refine Finset.sum_congr rfl (fun v2 hv2 => ?_)
  have hv1 : v1 ≠ u := by
    have hv2' : (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u := by
      simpa [Finset.mem_filter, Finset.mem_univ, true_and] using hv2
    exact hv2'.1.2
  have hv2u : v2 ≠ u := by
    have hv2' : (v2 ≠ v1 ∧ v1 ≠ u) ∧ v2 ≠ u := by
      simpa [Finset.mem_filter, Finset.mem_univ, true_and] using hv2
    exact hv2'.2
  simp [NeuralNetwork.State.Wact,
    sPos_act_of_ne (s := s) hv1, sNeg_act_of_ne (s := s) hv1,
    sPos_act_of_ne (s := s) hv2u, sNeg_act_of_ne (s := s) hv2u]

-- The changing part of `Ew_update_formula_split`, computed explicitly.
set_option maxHeartbeats 1200000 in
lemma Ew_main_diff_sPos_sNeg (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    (- ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sPos s u).Wact (wθ := p) v2 u)
      -
    (- ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sNeg s u).Wact (wθ := p) v2 u)
      =
    - (2 : R) * field p s u := by
  classical
  -- Compute the non-negated difference first.
  have hsum :
      (∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sPos s u).Wact (wθ := p) v2 u)
        -
      (∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sNeg s u).Wact (wθ := p) v2 u)
        =
      (2 : R) * field p s u := by
    -- Factor out `act u` and use symmetry to match `field`.
    let B : R := ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U), p.w v2 u * s.act v2
    have hB : B = ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U), p.w u v2 * s.act v2 := by
      unfold B
      refine Finset.sum_congr rfl (fun v2 hv2 => ?_)
      simp [w_symm (p := p) (i := v2) (j := u), mul_assoc]
    have hfield : field p s u = B := by
      -- `field` uses `p.w u v2`; rewrite using `hB`.
      simp [field, hB]
    have hsumPos :
        (∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
            (sPos s u).Wact (wθ := p) v2 u)
          =
        B * (sPos s u).act u := by
      let S0 : Finset U := ({v2 : U | v2 ≠ u} : Finset U)
      have hrewrite :
          (∑ v2 ∈ S0, (sPos s u).Wact (wθ := p) v2 u)
            =
          ∑ v2 ∈ S0, (p.w v2 u * s.act v2) * (sPos s u).act u := by
        refine Finset.sum_congr rfl (fun v2 hv2 => ?_)
        have hv2u : v2 ≠ u := by
          simpa [S0, Finset.mem_filter, Finset.mem_univ, true_and] using hv2
        simp [NeuralNetwork.State.Wact, sPos_act_of_ne (s := s) hv2u, mul_assoc]
      -- `B` is the same sum as on the RHS.
      unfold B
      -- rewrite and close by `sum_mul`.
      rw [hrewrite]
      simpa [S0, mul_assoc] using
        (Finset.sum_mul (s := S0) (f := fun v2 => p.w v2 u * s.act v2)
          ((sPos s u).act u)).symm
    have hsumNeg :
        (∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
            (sNeg s u).Wact (wθ := p) v2 u)
          =
        B * (sNeg s u).act u := by
      let S0 : Finset U := ({v2 : U | v2 ≠ u} : Finset U)
      have hrewrite :
          (∑ v2 ∈ S0, (sNeg s u).Wact (wθ := p) v2 u)
            =
          ∑ v2 ∈ S0, (p.w v2 u * s.act v2) * (sNeg s u).act u := by
        refine Finset.sum_congr rfl (fun v2 hv2 => ?_)
        have hv2u : v2 ≠ u := by
          simpa [S0, Finset.mem_filter, Finset.mem_univ, true_and] using hv2
        simp [NeuralNetwork.State.Wact, sNeg_act_of_ne (s := s) hv2u, mul_assoc]
      unfold B
      rw [hrewrite]
      simpa [S0, mul_assoc] using
        (Finset.sum_mul (s := S0) (f := fun v2 => p.w v2 u * s.act v2)
          ((sNeg s u).act u)).symm
    -- Put together.
    calc
      (∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sPos s u).Wact (wθ := p) v2 u)
        -
      (∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sNeg s u).Wact (wθ := p) v2 u)
        = B * ((sPos s u).act u - (sNeg s u).act u) := by
            rw [hsumPos, hsumNeg]; ring_nf
    _ = (2 : R) * field p s u := by
          rw [sPos_act_self (s := s) u, sNeg_act_self (s := s) u, hfield]
          ring_nf
  -- Negate the difference: `(-A) - (-B) = -(A - B)` and use `hsum`.
  set A : R := ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U), (sPos s u).Wact (wθ := p) v2 u
  set B' : R := ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U), (sNeg s u).Wact (wθ := p) v2 u
  have hneg : (-A) - (-B') = -(A - B') := by
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  calc
    (- ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sPos s u).Wact (wθ := p) v2 u)
      -
    (- ∑ v2 ∈ ({v2 : U | v2 ≠ u} : Finset U),
          (sNeg s u).Wact (wθ := p) v2 u)
        = (-A) - (-B') := by simp [A, B']
    _ = -(A - B') := hneg
    _ = - ((2 : R) * field p s u) := by
          rw [hsum]
    _ = - (2 : R) * field p s u := by ring_nf

set_option maxHeartbeats 1200000 in
lemma Ew_diff_sPos_sNeg (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    (NeuralNetwork.State.Ew (s := (sPos s u)) (wθ := p)) -
      (NeuralNetwork.State.Ew (s := (sNeg s u)) (wθ := p))
      = - (2 : R) * field p s u := by
  classical
  -- Use the split formula for both states and cancel the rest term.
  have hsplit_pos := (Ew_update_formula_split (s := (sPos s u)) (wθ := p) (u := u))
  have hsplit_neg := (Ew_update_formula_split (s := (sNeg s u)) (wθ := p) (u := u))
  -- Rewrite and cancel.
  rw [hsplit_pos, hsplit_neg]
  -- Cancel the rest term via `Ew_rest_eq_sPos_sNeg`, then use `Ew_main_diff_sPos_sNeg`.
  have hrest := Ew_rest_eq_sPos_sNeg (p := p) (s := s) (u := u)
  have hmain := Ew_main_diff_sPos_sNeg (p := p) (s := s) (u := u)
  -- rewrite the `sPos` rest term into the `sNeg` rest term, then cancel without unfolding `Wact`
  rw [hrest]
  -- `(a + r) - (b + r) = a - b`
  simpa [add_sub_add_right_eq_sub] using hmain

set_option maxHeartbeats 800000 in
-- The key structural lemma: in a symmetric Hopfield energy, the difference between the two forced
-- flips is exactly `-2 * localField`.
lemma flip_energy_relation_R
    (p : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) :
    E (R := R) (U := U) p (sPos s u) - E (R := R) (U := U) p (sNeg s u)
      = - (2 : R) * localField (R := R) (U := U) p s u := by
  classical
  have hEθ := Eθ_diff_sPos_sNeg (p := p) (s := s) (u := u)
  have hEw := Ew_diff_sPos_sNeg (p := p) (s := s) (u := u)
  have hlf := localField_eq_field_sub_θu (p := p) (s := s) (u := u)
  have hE :
      E (R := R) (U := U) p (sPos s u) -
          E (R := R) (U := U) p (sNeg s u)
        =
        (- (2 : R) * field p s u) + ((2 : R) * θu p u) := by
    -- Unfold energy and split into Ew/Eθ parts without `simp` search.
    dsimp [E]
    dsimp [NeuralNetwork.State.E]
    -- Regroup into the two component differences, then substitute them.
    have hsplit :
        ((NeuralNetwork.State.Ew (s := (sPos s u)) (wθ := p) +
              NeuralNetwork.State.Eθ (s := (sPos s u)) (wθ := p)) -
            (NeuralNetwork.State.Ew (s := (sNeg s u)) (wθ := p) +
              NeuralNetwork.State.Eθ (s := (sNeg s u)) (wθ := p)))
          =
        ((NeuralNetwork.State.Ew (s := (sPos s u)) (wθ := p) -
              NeuralNetwork.State.Ew (s := (sNeg s u)) (wθ := p)) +
          (NeuralNetwork.State.Eθ (s := (sPos s u)) (wθ := p) -
              NeuralNetwork.State.Eθ (s := (sNeg s u)) (wθ := p))) := by
      ring_nf
    rw [hsplit, hEw, hEθ]
    ring_nf; aesop
  calc
    E (R := R) (U := U) p (sPos s u) -
        E (R := R) (U := U) p (sNeg s u)
        =
        (- (2 : R) * field p s u) + ((2 : R) * θu p u) := hE
    _ = - (2 : R) * (field p s u - θu p u) := by ring_nf
    _ = - (2 : R) * localField (R := R) (U := U) p s u := by
          -- rewrite `field - θu` as `localField` using `hlf.symm`
          simpa using congrArg (fun z => - (2 : R) * z) hlf.symm

-- Package the above into an `EnergySpec'` for the Hopfield network.
noncomputable def spec :
    TwoState.EnergySpec' (R := R) (U := U) (σ := R) (NN := HopfieldNetwork R U) where
  E := E (R := R) (U := U)
  localField := localField (R := R) (U := U)
  localField_spec := by
    intro p s u
    rfl
  flip_energy_relation := by
    intro f p s u
    have hR := flip_energy_relation_R (R := R) (U := U) (p := p) (s := s) (u := u)
    have hscale :
        TwoState.scale (R := R) (U := U) (σ := R) (NN := HopfieldNetwork R U) (f := f) = f 2 := by
      unfold TwoState.scale
      -- For Hopfield, `m = id`, `σ_pos = 1`, `σ_neg = -1`, hence `scale = f 1 - f (-1) = f 2`.
      simp [instTwoStateHopfield, HopfieldNetwork, sub_neg_eq_add, one_add_one_eq_two, map_ofNat]
    -- Push forward the `R`-identity along `f`, then rewrite `scale`.
    have hf : f (E (R := R) (U := U) p (sPos (R := R) (U := U) s u) -
                E (R := R) (U := U) p (sNeg (R := R) (U := U) s u))
              =
              f (-(2 : R) * localField (R := R) (U := U) p s u) := by
      simp [hR]
    -- Normalize to the spec's RHS.
    -- `f (-(2:R) * L) = - (f 2) * f L = - (scale f) * f L`.
    simpa [hscale, map_neg, map_mul, mul_assoc] using hf

end HopfieldEnergySpec

end NeuralNetwork
