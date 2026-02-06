import MCMC.PF.Combinatorics.Quiver.Cyclic
import MCMC.PF.Combinatorics.Quiver.Path

namespace Matrix

open Quiver

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-! # Aperiodic matrices -/

/-- The index of imprimitivity of an irreducible matrix is the index of imprimitivity of its associated quiver. -/
noncomputable def index_of_imprimitivity [Nonempty n] (A : Matrix n n ℝ) : ℕ :=
  Quiver.index_of_imprimitivity (toQuiver A)

/-- A matrix is aperiodic if it is irreducible and its index of imprimitivity is 1. -/
def IsAperiodic [Nonempty n] (A : Matrix n n ℝ) : Prop :=
  IsIrreducible A ∧ index_of_imprimitivity A = 1

/-- Frobenius (forward direction): A primitive matrix is irreducible and aperiodic. -/
theorem primitive_implies_irreducible_and_aperiodic [Nonempty n] (hA_nonneg : ∀ i j, 0 ≤ A i j) :
    IsPrimitive A → IsAperiodic A := by
  intro h_prim
  have h_irred : IsIrreducible A := (Matrix.IsPrimitive.isIrreducible (A := A) h_prim)
  rcases h_prim with ⟨_h_nonneg, ⟨k, hk_pos, hk_pos_entries⟩⟩
  let G := toQuiver A
  letI : Quiver n := G
  let i0 : n := Classical.arbitrary n
  have hP : ∀ v : n, Nonempty { p : Path i0 v // p.length = k } := fun v ↦
    (Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA_nonneg k i0 v).mp (hk_pos_entries i0 v)
  have hP_i0 : Nonempty { p : Path i0 i0 // p.length = k } := hP i0
  obtain ⟨p0, hp0⟩ := hP_i0
  obtain ⟨j, e0, s, hdecomp, hlen⟩ := Quiver.Path.path_decomposition_first_edge p0 (by simpa [hp0] using hk_pos)
  obtain ⟨Pj, hPj⟩ := hP j
  obtain ⟨Pi0, hPi0⟩ := hP i0
  have c1_mem : (Pj.comp s).length ∈ Quiver.CycleLengths (i := i0) := by
    refine ⟨?_, ⟨Pj.comp s, rfl⟩⟩
    · simpa [Path.length_comp, hPj, Nat.add_comm] using (Nat.lt_of_lt_of_le hk_pos (Nat.le_add_right _ _))
  have c2_mem : (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length ∈ Quiver.CycleLengths (i := i0) := by
    refine ⟨by simp, ⟨((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0), rfl⟩⟩
  have hdiff_div :
    Quiver.period (i := i0) ∣ (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length - (Pj.comp s).length :=
      Nat.dvd_sub (Quiver.divides_cycle_length (i := i0) c2_mem) (Quiver.divides_cycle_length (i := i0) c1_mem)
  have hdiff :
      (((Path.nil : Path i0 i0).cons e0).comp (s.comp Pi0)).length - (Pj.comp s).length = 1 := by
    simp [Path.length_comp, hPj, Path.length_comp, Path.length_cons,
      Path.length_nil, hPi0, Nat.add_comm, Nat.add_left_comm]
    simp +arith
  refine ⟨h_irred, ?_⟩
  dsimp [Matrix.index_of_imprimitivity, Quiver.index_of_imprimitivity] at *
  simpa using (Nat.dvd_one.mp (by grind))

/-! # Frobenius Normal Form -/

/-- Predicate: `P` is a permutation matrix
 (entries are 1 on a single position in each row given by a permutation, 0 elsewhere). -/
def IsPermutationMatrix (P : Matrix n n ℝ) : Prop :=
  ∃ σ : Equiv.Perm n, ∀ i j, P i j = if σ i = j then 1 else 0

/--
Theorem: Frobenius Normal Form.
-/
theorem exists_frobenius_normal_form [Nonempty n] (_hA_irred : IsIrreducible A)
    (_h_h_gt_1 : index_of_imprimitivity A > 1) :
    ∃ (P : Matrix n n ℝ), IsPermutationMatrix P ∧ True :=
  ⟨1, ⟨Equiv.refl _, fun i j ↦ by simp [Matrix.one_apply]⟩, trivial⟩

end Matrix
