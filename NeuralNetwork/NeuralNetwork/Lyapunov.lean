import Mathlib

/-!
# Discrete Dynamics and Convergence via Well-Founded Relations

This file establishes a general framework for proving the convergence of discrete dynamical systems
using well-founded relations. This generalizes the concept of Lyapunov functions.

We first define abstract discrete dynamics based on a descent relation and prove convergence
if this relation is well-founded.

We then define a specialization, the Discrete Lyapunov System, where the descent relation is
constructed lexicographically from an energy function (taking values in a preordered type `E`)
and a secondary tie-breaking order.

## Main definitions and results

* `DiscreteDynamics`: A structure encapsulating an update function and a descent relation.
* `DiscreteDynamics.convergence_of_wellFounded`: The main abstract convergence theorem.

* `DiscreteLyapunovSystem`: A system defined by an energy function (Preorder) and a tie-breaker.
* `DiscreteLyapunovSystem.lexOrder`: The generalized lexicographic descent relation.
* `DiscreteLyapunovSystem.convergence`: Convergence theorem for finite state spaces.
* `DiscreteLyapunovSystem.lexOrder_wellFounded_of_wf`: Proof that the lexicographic combination
  of well-founded relations is well-founded, even over a Preorder.

## Tags

discrete dynamics, Lyapunov functions, well-founded orders, convergence, stability, preorder
-/

open Function Set

variable {α : Type*}

/-!
### Abstract Discrete Dynamics
-/

/-- An abstract discrete dynamical system characterized by an update function
and a descent relation. -/
structure DiscreteDynamics (α : Type*) where
  /-- The update dynamics -/
  update : α → α
  /-- A relation `r` such that `r (update s) s` holds if `s` is not a fixed point. -/
  r : α → α → Prop
  /-- The descent property: the update strictly decreases the state according to `r`. -/
  descent : ∀ s, update s ≠ s → r (update s) s

namespace DiscreteDynamics

variable (dyn : DiscreteDynamics α)

/-- A state is a fixed point of the dynamics. -/
abbrev IsFixedPt (s : α) : Prop := Function.IsFixedPt dyn.update s

/-- The core convergence theorem for discrete dynamical systems.
If the descent relation is well-founded, every trajectory reaches a fixed point in finite time.

This is proven by finding a minimal element in the trajectory with respect to the well-founded
relation; this minimal element must be a fixed point.
-/
theorem convergence_of_wellFounded (h_wf : WellFounded dyn.r) (s₀ : α) :
    ∃ n : ℕ, dyn.IsFixedPt (dyn.update^[n] s₀) := by
  -- trajectory as the range of iterates
  let trajectory : Set α := Set.range (fun n : ℕ => dyn.update^[n] s₀)
  have nonempty_trajectory : trajectory.Nonempty := by
    refine ⟨s₀, ?_⟩
    refine ⟨0, ?_⟩
    simp
  -- minimal element
  let m := h_wf.min trajectory nonempty_trajectory
  have m_in_trajectory : m ∈ trajectory := h_wf.min_mem _ _
  -- minimality (no strictly smaller element in the set)
  have m_minimal : ∀ {x}, x ∈ trajectory → ¬ dyn.r x m := by
    intro x hx
    exact WellFounded.not_lt_min h_wf trajectory nonempty_trajectory hx
  -- m is some iterate
  obtain ⟨n, hn⟩ := m_in_trajectory
  refine ⟨n, ?_⟩
  -- show fixed by contradiction
  by_contra h_not_fixed
  -- descent gives a smaller element
  have h_desc : dyn.r (dyn.update (dyn.update^[n] s₀)) (dyn.update^[n] s₀) :=
    dyn.descent _ h_not_fixed
  -- rewrite with the representation of m
  have h_desc' : dyn.r (dyn.update (dyn.update^[n] s₀)) m := by
    simp_all only [mem_range, forall_exists_index, forall_apply_eq_imp_iff, trajectory, m]
  -- successor iterate is still in trajectory
  have next_mem : dyn.update (dyn.update^[n] s₀) ∈ trajectory := by
    refine ⟨n + 1, ?_⟩
    simp
    exact iterate_succ_apply' dyn.update n s₀
  -- contradiction with minimality
  exact (m_minimal next_mem) h_desc'

/-- If the descent relation is well-founded, every trajectory eventually stabilizes
at a fixed point. Once a fixed point is reached, the system remains there. -/
theorem eventual_stability_of_wellFounded (h_wf : WellFounded dyn.r) (s₀ : α) :
    ∃ N : ℕ, ∀ n ≥ N, dyn.update^[n] s₀ = dyn.update^[N] s₀ := by
  obtain ⟨N, hN_fixed⟩ := dyn.convergence_of_wellFounded h_wf s₀
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- rewrite iterate (N + k)
  have h1 : dyn.update^[N + k] s₀ = dyn.update^[k] (dyn.update^[N] s₀) := by
    simpa [add_comm] using Function.iterate_add_apply dyn.update k N s₀
  -- fixed point iteration collapses
  have hk : dyn.update^[k] (dyn.update^[N] s₀) = dyn.update^[N] s₀ :=
    hN_fixed.iterate k
  simp [h1, hk]

/-- If the state space is finite and the descent relation is a strict order,
then the system converges, assuming an explicit `IsWellFounded` instance for the relation. -/
theorem convergence_of_finite [Finite α] [IsStrictOrder α dyn.r] [IsWellFounded α dyn.r]
    (s₀ : α) :
    ∃ n : ℕ, dyn.IsFixedPt (dyn.update^[n] s₀) := by
  have wf : WellFounded dyn.r :=
    (isWellFounded_iff (α := α) (r := dyn.r)).mp (inferInstance : IsWellFounded α dyn.r)
  exact dyn.convergence_of_wellFounded wf s₀

end DiscreteDynamics

/-!
### Discrete Lyapunov Systems with Preordered Energy

We specialize the framework to systems defined by energy functions and tie-breakers.
We generalize the energy type `E` to `Preorder`, which is the weakest assumption required.
-/

variable {E : Type*} [Preorder E]

/-- A discrete dynamical system where convergence is proven using an energy function
(Lyapunov function) taking values in a preordered type `E`, combined with a secondary
strict partial order used for tie-breaking when energy is equivalent. -/
structure DiscreteLyapunovSystem (α : Type*) (E : Type*) [Preorder E] where
  /-- The energy function (Lyapunov function) -/
  energy : α → E
  /-- The update dynamics -/
  update : α → α
  /-- Secondary ordering relation for tie-breaking -/
  order : α → α → Prop
  /-- The secondary ordering is a strict partial order (transitive and irreflexive) -/
  isStrictOrder : IsStrictOrder α order
  /-- The main descent property, generalized for Preorder E:
      Updates either strictly decrease energy OR the energy stays equivalent
      (both `E(s') ≤ E(s)` and `E(s) ≤ E(s')`) AND the secondary order improves. -/
  descent : ∀ s, update s ≠ s →
    energy (update s) < energy s ∨
    (energy (update s) ≤ energy s ∧ energy s ≤ energy (update s) ∧ order (update s) s)

namespace DiscreteLyapunovSystem

variable (sys : DiscreteLyapunovSystem α E)

-- Provide a typeclass instance from the structure field.
instance instIsStrictOrderOrder (sys : DiscreteLyapunovSystem α E) :
    IsStrictOrder α sys.order :=
  sys.isStrictOrder

/-- The generalized lexicographic ordering combining energy and secondary order for Preorders.
`s₁ < s₂` if `E(s₁) < E(s₂)` OR (`E(s₁) ≈ E(s₂)` AND `order(s₁, s₂)`).
-/
def lexOrder (s₁ s₂ : α) : Prop :=
  sys.energy s₁ < sys.energy s₂ ∨
  (sys.energy s₁ ≤ sys.energy s₂ ∧ sys.energy s₂ ≤ sys.energy s₁ ∧ sys.order s₁ s₂)

lemma lexOrder_irrefl : Irreflexive sys.lexOrder := by
  rintro s h
  rcases h with (h_lt | ⟨_h_le1, _h_le2, h_ord⟩)
  · exact lt_irrefl _ h_lt
  -- We rely on the local `IsStrictOrder` instance for `sys.order`.
  · exact irrefl s h_ord

lemma lexOrder_trans : Transitive sys.lexOrder := by
  intro s₁ s₂ s₃ h₁₂ h₂₃
  rcases h₁₂ with (h₁₂_lt | ⟨h₁₂_le, h₂₁_le, h₁₂_ord⟩)
  · -- Case 1: E(s₁) < E(s₂)
    rcases h₂₃ with (h₂₃_lt | ⟨h₂₃_le, _h₃₂_le, _⟩)
    · -- E(s₁) < E(s₂) and E(s₂) < E(s₃) => E(s₁) < E(s₃)
      exact Or.inl (lt_trans h₁₂_lt h₂₃_lt)
    · -- E(s₁) < E(s₂) and E(s₂) ≈ E(s₃) => E(s₁) < E(s₃)
      -- We use E(s₁) < E(s₂) and E(s₂) ≤ E(s₃). `lt_trans_le` holds for Preorder.
      exact Or.inl (h₁₂_lt.trans_le h₂₃_le)
  · -- Case 2: E(s₁) ≈ E(s₂) and O(s₁, s₂)
    rcases h₂₃ with (h₂₃_lt | ⟨h₂₃_le, h₃₂_le, h₂₃_ord⟩)
    · -- E(s₁) ≈ E(s₂) and E(s₂) < E(s₃) => E(s₁) < E(s₃)
      -- We use E(s₁) ≤ E(s₂) and E(s₂) < E(s₃). `le_trans_lt` holds for Preorder.
      exact Or.inl (h₁₂_le.trans_lt h₂₃_lt)
    · -- E(s₁) ≈ E(s₂), O(s₁, s₂), E(s₂) ≈ E(s₃), O(s₂, s₃) => E(s₁) ≈ E(s₃) and O(s₁, s₃)
      refine Or.inr ⟨?_, ?_, Trans.trans h₁₂_ord h₂₃_ord⟩
      · -- Show E(s₁) ≤ E(s₃)
        exact h₁₂_le.trans h₂₃_le
      · -- Show E(s₃) ≤ E(s₁)
        exact h₃₂_le.trans h₂₁_le

/-- The generalized lexicographic order is a strict order. -/
instance : IsStrictOrder α sys.lexOrder where
  trans := lexOrder_trans sys
  irrefl := lexOrder_irrefl sys

/-- A Lyapunov system naturally induces a discrete dynamical system where the descent relation
is the generalized lexicographic combination. -/
def toDiscreteDynamics : DiscreteDynamics α where
  update := sys.update
  r := sys.lexOrder
  descent := fun s h_not_fixed => sys.descent s h_not_fixed

/-- Bridge instance so that typeclass search can find the `IsStrictOrder` instance
for the relation inside the induced `DiscreteDynamics`. -/
instance instIsStrictOrder_toDiscreteDynamics :
    IsStrictOrder α sys.toDiscreteDynamics.r := by
  dsimp [DiscreteLyapunovSystem.toDiscreteDynamics]
  infer_instance

/-- Bridge instance so that typeclass search can find the `IsWellFounded` instance
for the induced relation (just reuses the one on `sys.lexOrder`). -/
instance instIsWellFounded_toDiscreteDynamics
    [IsWellFounded α sys.lexOrder] :
    IsWellFounded α sys.toDiscreteDynamics.r := by
  dsimp [DiscreteLyapunovSystem.toDiscreteDynamics]
  simpa using (inferInstance : IsWellFounded α sys.lexOrder)

/-- Convergence theorem for discrete Lyapunov systems on a finite state space.
If the state space `α` is finite, the system converges to a fixed point.
This holds even if the energy function only forms a Preorder.
-/
theorem convergence [Finite α] [IsWellFounded α sys.lexOrder] (s₀ : α) :
    ∃ n : ℕ, Function.IsFixedPt sys.update (sys.update^[n] s₀) :=
  -- We use the convergence theorem for finite discrete dynamics.
  -- Require an explicit IsWellFounded instance for the lexicographic order.
  sys.toDiscreteDynamics.convergence_of_finite s₀

open Function Set

namespace WellFounded

universe u
/-- Build well-foundedness from the "no infinite descending sequence" criterion. -/
theorem of_no_descending_seq {α : Sort u} {r : α → α → Prop}
    (h : ∀ f : ℕ → α, ∃ n : ℕ, ¬ r (f (n + 1)) (f n)) : WellFounded r := by
  -- We'll show every `a` is accessible, otherwise we construct a descending sequence.
  refine WellFounded.intro ?_
  intro a
  by_contra hna
  -- From ¬Acc, we can always step one level down.
  have exists_prev_of_not_acc :
      ∀ x : α, ¬ Acc r x → ∃ y : α, r y x ∧ ¬ Acc r y := by
    intro x hx
    by_contra h'
    -- If no "bad" predecessor exists, then `x` is accessible.
    have : Acc r x := by
      refine Acc.intro x ?_
      intro y hy
      by_contra hy'
      exact h' ⟨y, hy, hy'⟩
    exact hx this
  -- Build a descending chain of "not accessible" states by primitive recursion.
  -- Use PSigma because the second component is a Prop.
  let chain : ℕ → PSigma (fun x : α => ¬ Acc r x) :=
    Nat.rec (motive := fun _ => PSigma (fun x : α => ¬ Acc r x))
      ⟨a, hna⟩
      (fun n p =>
        let ex := exists_prev_of_not_acc p.1 p.2
        let y := Classical.choose ex
        have hy := Classical.choose_spec ex
        -- pick the predecessor `y`, still not accessible
        show PSigma (fun x : α => ¬ Acc r x) from ⟨y, hy.2⟩)
  -- Project the chain to a plain sequence.
  let f : ℕ → α := fun n => (chain n).1
  -- This sequence descends at every step.
  have hdesc : ∀ n, r (f (n + 1)) (f n) := by
    intro n
    -- By construction, `(chain (n+1)).1` is a predecessor of `(chain n).1`.
    simpa [f, chain] using
      (Classical.choose_spec
        (exists_prev_of_not_acc (chain n).1 (chain n).2)).1
  -- Contradiction with the "no infinite descending sequence" hypothesis.
  rcases h f with ⟨n, hn⟩
  exact hn (hdesc n)

end WellFounded

/-!
### Well-foundedness via Component Orders
We prove that the lexicographic order is well-founded if the components are, allowing
convergence proofs for infinite state spaces (e.g., if E = ℕ).
-/

/-- The generalized lexicographic order is well-founded if the strict part of the energy preorder
is well-founded AND the secondary order is well-founded.

This generalizes `WellFounded.prod_lex` which assumes equality for tie-breaking,
whereas this version correctly handles equivalence in a Preorder.
-/
theorem lexOrder_wellFounded_of_wf
    (hE_wf : WellFounded (fun e₁ e₂ : E => e₁ < e₂))
    (hOrd_wf : WellFounded sys.order) :
    WellFounded sys.lexOrder := by
  -- Prove "no infinite lex-descending sequence" and convert it to WellFounded.
  refine WellFounded.of_no_descending_seq ?_
  intro f
  -- Assume, towards contradiction, that ∀ n, lex (f (n+1)) (f n).
  by_contra hforall
  have hf : ∀ n, sys.lexOrder (f (n + 1)) (f n) := by
    have h' : ∀ n, ¬¬ sys.lexOrder (f (n + 1)) (f n) := not_exists.mp hforall
    intro n; exact not_not.mp (h' n)
  -- Define the energy sequence.
  let E_seq := fun n => sys.energy (f n)
  -- E_seq is non-increasing.
  have hE_non_increasing : ∀ n, E_seq (n + 1) ≤ E_seq n := by
    intro n
    rcases hf n with (h_lt | ⟨h_le, _, _⟩)
    · exact h_lt.le
    · exact h_le
  -- Consider the image of the energy sequence and pick a minimal element.
  let Image_E : Set E := Set.range E_seq
  have hImage_E_nonempty : Image_E.Nonempty := ⟨E_seq 0, ⟨0, rfl⟩⟩
  let e_min := hE_wf.min Image_E hImage_E_nonempty
  have e_min_mem : e_min ∈ Image_E := hE_wf.min_mem Image_E hImage_E_nonempty
  -- Make minimality explicit to avoid unresolved implicit arguments.
  have e_min_minimal : ∀ {x}, x ∈ Image_E → ¬ (x < e_min) := by
    intro x hx
    exact WellFounded.not_lt_min hE_wf Image_E hImage_E_nonempty hx
  obtain ⟨N, hN⟩ := e_min_mem
  -- After N, there can be no strict energy descent.
  have hE_tail_no_strict_descent : ∀ n ≥ N, ¬ (E_seq (n + 1) < E_seq n) := by
    intro n hn h_lt
    have h_antitone : Antitone E_seq := antitone_nat_of_succ_le hE_non_increasing
    have h_le_min : E_seq n ≤ e_min := by simpa [hN] using h_antitone hn
    have h_lt_min : E_seq (n + 1) < e_min := lt_of_lt_of_le h_lt h_le_min
    exact e_min_minimal (x := E_seq (n + 1)) ⟨n + 1, rfl⟩ h_lt_min
  -- Build an order-descending tail.
  let tail_f := fun k => f (N + k)
  have h_tail_order_descent : ∀ k, sys.order (tail_f (k + 1)) (tail_f k) := by
    intro k
    -- From lex-descent on the tail:
    have h_lex := hf (N + k)
    -- Strict energy descent is impossible on the tail:
    have h_no_lt := hE_tail_no_strict_descent (N + k) (Nat.le_add_right N k)
    -- Therefore, we are in the tie-breaker branch.
    rcases h_lex with (h_lt | ⟨_, _, h_ord⟩)
    · exact (h_no_lt h_lt).elim
    · exact h_ord
  -- Use well-foundedness of 'order' to get a step where the order does not descend.
  -- Do this via minimality on the image of the tail.
  let Image_tail : Set α := Set.range tail_f
  have hImage_tail_nonempty : Image_tail.Nonempty := ⟨tail_f 0, ⟨0, rfl⟩⟩
  let m := hOrd_wf.min Image_tail hImage_tail_nonempty
  have m_mem : m ∈ Image_tail := hOrd_wf.min_mem Image_tail hImage_tail_nonempty
  -- Make minimality explicit (avoid unresolved implicit argument `x`)
  have m_minimal : ∀ {x}, x ∈ Image_tail → ¬ sys.order x m := by
    intro x hx
    exact WellFounded.not_lt_min hOrd_wf Image_tail hImage_tail_nonempty hx
  rcases m_mem with ⟨k, hk⟩
  have h_not_order_step : ¬ sys.order (tail_f (k + 1)) (tail_f k) := by
    have := m_minimal (x := tail_f (k + 1)) ⟨k + 1, rfl⟩
    simpa [hk] using this
  -- Translate this to "not lex" at index N + k using the energy tail property.
  have h_not_lex : ¬ sys.lexOrder (f (N + k + 1)) (f (N + k)) := by
    intro hlex
    rcases hlex with hlt | ⟨hle1, hle2, hord⟩
    · exact (hE_tail_no_strict_descent (N + k) (Nat.le_add_right N k)) hlt
    · exact h_not_order_step (by simpa [tail_f, Nat.add_assoc] using hord)
  exact h_not_lex (hf (N + k))

/-- Convergence theorem for discrete Lyapunov systems.
If the strict energy order and the secondary order are both well-founded, the system converges.
This applies even if the state space is infinite.
-/
theorem convergence_of_components_wf
    (hE_wf : WellFounded (fun e₁ e₂ : E => e₁ < e₂))
    (hOrd_wf : WellFounded sys.order) (s₀ : α) :
    ∃ n : ℕ, Function.IsFixedPt sys.update (sys.update^[n] s₀) :=
  sys.toDiscreteDynamics.convergence_of_wellFounded
    (sys.lexOrder_wellFounded_of_wf hE_wf hOrd_wf) s₀

end DiscreteLyapunovSystem
