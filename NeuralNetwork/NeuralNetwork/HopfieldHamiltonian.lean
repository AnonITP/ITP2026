import NeuralNetwork.NeuralNetwork.Core
import NeuralNetwork.NeuralNetwork.toCanonicalEnsemble

/-!
# Hopfield networks are Hamiltonian (SOTA bridge)

This file connects the constructive Hopfield development in `NeuralNetwork/NeuralNetwork/Core.lean`
to the statistical mechanics layer in `NeuralNetwork/NeuralNetwork/toCanonicalEnsemble.lean`.

Concretely:
- we instantiate `IsHamiltonian` for `HopfieldNetwork ℝ U`,
- using the already-proved Lyapunov property `energy_diff_leq_zero` from the Hopfield core.

This makes all CanonicalEnsemble / thermodynamics / MCMC tooling available.
-/

open scoped BigOperators

namespace NeuralNetwork

open NeuralNetwork.State

variable {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]

-- For finite state spaces we use the trivial σ-algebra (as in `toCanonicalEnsemble.lean`).
instance : MeasurableSpace ( (HopfieldNetwork ℝ U).State ) := ⊤

noncomputable instance : IsHamiltonian (U := U) (σ := ℝ) (HopfieldNetwork ℝ U) where
  energy p s := s.E (wθ := p)
  energy_measurable := by
    intro p
    -- finite state space ⇒ measurability is trivial
    simp
  energy_is_lyapunov := by
    intro p s u
    -- Either the site changes (strict Lyapunov lemma) or the update is a no-op (energy unchanged).
    by_cases h : (s.Up p u).act u = s.act u
    · have hup : s.Up p u = s := by
        -- Reuse the Hopfield core lemma relating act equality to state equality.
        -- (`State'` is just an alias for the state type.)
        simpa [State', Up'] using (state_Up_act (wθ := p) (u := u) (s := (s : State' p)) h)
      -- energy is equal under no-op update
      simp [hup]
    · -- site changes ⇒ energy decreases
      -- `energy_diff_leq_zero` expects a strict inequality of the activation at `u`.
      have hc : (s.Up p u).act u ≠ s.act u := by exact h
      simpa [IsHamiltonian.energy] using (energy_diff_leq_zero (wθ := p) (s := s) (u := u) hc)

end NeuralNetwork
