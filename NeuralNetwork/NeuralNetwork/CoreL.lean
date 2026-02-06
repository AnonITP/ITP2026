import NeuralNetwork.NeuralNetwork.Lyapunov
import NeuralNetwork.NeuralNetwork.Core

open Finset Matrix NeuralNetwork State

universe uR uU

namespace HopfieldLyapunov

open NeuralNetwork

variable {R : Type uR} {U : Type uU}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [DecidableEq U] [Fintype U] [Nonempty U]

variable (wθ : Params (HopfieldNetwork R U))

-- Secondary strict order: tie-breaker is the number of pluses (more pluses is "smaller").
def tieOrder (s₁ s₂ : (HopfieldNetwork R U).State) : Prop :=
  s₂.pluses < s₁.pluses

instance : IsStrictOrder ((HopfieldNetwork R U).State) (tieOrder) where
  irrefl := by
    intro s; exact lt_irrefl _
  trans := by
    intro a b c hab hbc
    -- hab : b.pluses < a.pluses, hbc : c.pluses < b.pluses
    exact lt_trans hbc hab

/-- Predicate: whether updating at `u` changes the state (explicit `wθ`). -/
@[inline] def changes (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) (u : U) : Prop :=
  (s.Up wθ u) ≠ s

/-- Pick an unstable neuron when the state is not stable (uses choice from ∃-witness). -/
noncomputable def pickUnstable (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State)
    (h : ¬ s.isStable wθ) : {u : U // (s.Up wθ u) ≠ s} :=
  let u := Classical.choose (not_stable_u (wθ := wθ) s h)
  let hu := Classical.choose_spec (not_stable_u (wθ := wθ) s h)
  ⟨u, hu⟩

/-- Greedy update: flip an unstable neuron if any; else do nothing. -/
noncomputable def updateGreedy (wθ : Params (HopfieldNetwork R U)) (s : (HopfieldNetwork R U).State) : (HopfieldNetwork R U).State :=
  if h : s.isStable wθ then s
  else
    let p := pickUnstable wθ s h
    s.Up wθ p.1

-- Greedy update is identity iff the state is stable.
lemma updateGreedy_fixed_iff_stable (s : (HopfieldNetwork R U).State) :
    updateGreedy wθ s = s ↔ s.isStable wθ := by
  constructor
  · -- If updateGreedy wθ s = s, then s.isStable wθ
    intro h
    by_contra hs
    -- If s is not stable, then updateGreedy would pick an unstable neuron and change s
    simp [updateGreedy, hs] at h
    let p := pickUnstable wθ s hs
    have hchange : (s.Up wθ p.1) ≠ s := p.2
    exact hchange h
  · -- If s.isStable wθ, then updateGreedy wθ s = s
    intro hs
    simp [updateGreedy, hs]

abbrev HState := (HopfieldNetwork R U).State

/-- HopfieldNetwork R U as a Lyapunov structure: energy, greedy update, and the tie-breaker. -/
noncomputable def sysGreedy :
  DiscreteLyapunovSystem ((HopfieldNetwork R U).State) R where
  energy s := s.E wθ
  update := updateGreedy wθ
  order := tieOrder
  isStrictOrder := inferInstance
  descent := by
    intro s
    simp [updateGreedy]
    split_ifs with h
    · -- Case: s.isStable wθ, so updateGreedy wθ s = s
      intro hcontra
      exfalso
      exact hcontra h
    · -- Case: ¬s.isStable wθ, so we pick an unstable neuron and update
      let p := pickUnstable wθ s h
      have hchange : (s.Up wθ p.1) ≠ s := p.2
      intro _
      intro _
      -- The theorem expects a change in activation, not in the entire state
      -- We need to show that the activation actually changes when the state changes
      have h_act_change : (s.Up wθ p.1).act p.1 ≠ s.act p.1 := by
        -- This follows from the fact that Up only changes the state if activation changes
        by_contra h_eq
        have h_up_eq : s.Up wθ p.1 = s := state_Up_act s h_eq
        exact hchange h_up_eq
      -- Now use the corrected theorem with activation change
      have h_energy := energy_lt_zero_or_pluses_increase wθ h_act_change
      cases h_energy with
      | inl h_lt =>
        exact Or.inl h_lt
      | inr h_eq_and_pluses =>
        exact Or.inr ⟨h_eq_and_pluses.1.le, h_eq_and_pluses.1.symm.le, h_eq_and_pluses.2⟩

-- For finite state space and strict lexicographic descent, the Lyapunov abstract theorem applies.
-- We use the convergence theorem from Lyapunov.lean on finite types.
theorem converges_to_fixed (s₀ : HState)
    [IsWellFounded (HState) (sysGreedy (wθ := wθ)).lexOrder] :
    ∃ n, Function.IsFixedPt (updateGreedy (wθ := wθ)) ((updateGreedy (wθ := wθ))^[n] s₀) :=
  (sysGreedy (wθ := wθ)).convergence s₀

-- Fixed point for updateGreedy is equivalent to network stability.
lemma fixed_isStable {s : HState} :
    Function.IsFixedPt (updateGreedy (wθ := wθ)) s ↔ s.isStable wθ := by
  constructor
  · intro h; exact (updateGreedy_fixed_iff_stable (wθ := wθ) s).mp h
  · intro hs; exact (updateGreedy_fixed_iff_stable (wθ := wθ) s).mpr hs

/-- Main Lyapunov-based convergence: reach a stable state in finitely many steps
    when `lexOrder` is well-founded. On a finite state space, you can either
    provide an `IsWellFounded` instance for `lexOrder` or reuse a local proof. -/
theorem converges_to_stable (s₀ : HState)
    [IsWellFounded (HState) (sysGreedy (wθ := wθ)).lexOrder] :
    ∃ n, (updateGreedy (wθ := wθ))^[n] s₀ |>.isStable wθ := by
  obtain ⟨n, hfix⟩ := converges_to_fixed (wθ := wθ) s₀
  refine ⟨n, ?_⟩
  simpa [fixed_isStable (wθ := wθ)] using hfix

end HopfieldLyapunov
