/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric

variable {U : Type*}  [Field R]

open Finset Fintype

lemma isSymm_sum (f : Fin m → Matrix U U R) (hi : ∀ i, (f i).IsSymm) : (∑ i, f i).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_sum univ f, Finset.sum_congr rfl]; exact fun x _ ↦ hi x

--def fair' (sseq : Nat → NN.State) : Prop := ∀ n, ∃ m > n, sseq (m + 1) ≠ sseq m

/--
A sequence `useq` is fair if for every element `u` and every index `n`,
there exists an index `m` greater than or equal to `n` such that `useq m = u`.
--/
def fair (useq : ℕ → U) : Prop := ∀ u n, ∃ m ≥ n, useq m = u

/--
`cyclic useq` is a property that holds if `useq` is a sequence such that:
1. Every element of type `U` appears at least once in the sequence.
2. The sequence is periodic with a period equal to the cardinality of `U`.
--/
def cyclic [Fintype U] (useq : ℕ → U) : Prop :=
  (∀ u : U, ∃ i, useq i = u) ∧ (∀ i j, i % card U = j % card U → useq i = useq j)

variable [Nonempty U]

lemma Fintype.exists_mod_eq_within_bounds [Fintype U] : ∀ i (n : ℕ),
    ∃ m ≥ n, m < n + card U ∧ m % card U = i % (card U) := by  {
  simp only [ge_iff_le]
  intros i n
  let a := (n / card U) + 1
  have : a * card U ≥ n := by {
    simp only [ge_iff_le]
    simp only [a]
    rw [add_mul]
    simp only [one_mul]
    rw [le_iff_lt_or_eq]
    left
    exact Nat.lt_div_mul_add Fintype.card_pos}
  let j := i + a * card U
  have hj : j ≥ n := by {
    simp only [j]
    exact le_add_of_le_right this}
  use (n + (j - n) % card U)
  constructor
  · simp only [ge_iff_le, a, j] at *
    exact Nat.le_add_right n ((i + (n / Fintype.card U + 1) * Fintype.card U - n) % Fintype.card U)
  · constructor
    · simp only [add_lt_add_iff_left]
      exact Nat.mod_lt _ Fintype.card_pos
    · simp only [Nat.add_mod_mod]
      simp_all only [ge_iff_le, add_tsub_cancel_of_le, Nat.add_mul_mod_self_right, a, j]}

lemma cycl_Fair [Fintype U] (useq : ℕ → U) : cyclic useq → fair useq := fun ⟨hcov, hper⟩ u n =>
  let ⟨i, hi⟩ := hcov u
  let ⟨m, hm, hkmod⟩ := @Fintype.exists_mod_eq_within_bounds U _ _ i n
  ⟨m, hm, hi ▸ hper m i hkmod.2⟩

lemma Fintype.cyclic_Fair_bound [Fintype U] (useq : ℕ → U) :
    cyclic useq → ∀ u (n : ℕ),
      ∃ m ≥ n, m < n + card U ∧ useq m = u := fun ⟨hcov, hper⟩ u n => by {
  obtain ⟨i, hi⟩ := hcov u
  have := @Fintype.exists_mod_eq_within_bounds U _ _ i n
  obtain ⟨m, hm, hle, hkmod⟩ := this
  use m
  constructor
  · exact hm
  · constructor
    · exact hle
    · rw [← hi]
      have := hper m i
      exact hper m i hkmod}

lemma sum_split (P Q : α → Prop) [DecidablePred P] [AddCommMonoid β]
    [DecidablePred Q] (f : α → β) :
  ∑ u ∈ filter (fun u => P u) s, f u = ∑ u ∈ filter (fun u => P u ∧ Q u) s, f u  +
      ∑ u ∈ filter (fun u => P u ∧ ¬ Q u) s, f u := by
  simp only [sum_filter, ← sum_add_distrib, ite_and, ite_add, ite_not, zero_add, add_zero, zero_add]
  apply Finset.sum_congr rfl; intros u _; split_ifs; rw [add_zero]; rfl; rfl

lemma sum_over_subset (f : α → β) (s : Finset α) [Fintype α] [AddCommMonoid β]
  [DecidablePred (fun x => x ∈ s)] :
  ∑ x ∈ s, f x = ∑ x, if x ∈ s then f x else 0 := by
  simp_rw [← sum_filter]; congr;
  ext; simp only [mem_filter, mem_univ, true_and]
