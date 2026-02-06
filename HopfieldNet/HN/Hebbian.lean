
import HopfieldNet.HN.Core

set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset

open Finset Matrix NeuralNetwork State Fintype

variable {R U : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq U] [Fintype U]
 [Nonempty U]

/--
Defines the Hebbian learning rule for a Hopfield Network.

Given a set of patterns `ps`, this function returns the network parameters
using the Hebbian learning rule, which adjusts weights based on pattern correlations.
-/
def Hebbian {m : ℕ} (ps : Fin m → (HopfieldNetwork R U).State) : Params (HopfieldNetwork R U) where
  /- The weight matrix, calculated as the sum of the outer products of the patterns minus
      a scaled identity matrix. -/
  w := ∑ k, outerProduct (ps k) (ps k) - (m : R) • (1 : Matrix U U R)
  /- The threshold function, which is set to a constant value of 0 for all units. -/
  θ u := ⟨#[0], rfl⟩
  /- The state function, which is set to an empty vector. -/
  σ _ := Vector.emptyWithCapacity 0
  /- A proof that the weight matrix is symmetric and satisfies the Hebbian learning rule. -/
  hw u v huv := by
    simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [Finset.sum_apply, Finset.sum_apply]
    have : ∀ k i, (ps k).act i * (ps k).act i = 1 := by
      intros k i ; rw [mul_self_eq_one_iff.mpr]; exact act_one_or_neg_one i
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    conv => enter [1, 1, 2];
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_apply_eq,
      sub_self]
  /- A proof that the weight matrix is symmetric. -/
  hw' := by
    simp only [Matrix.IsSymm,transpose_sub, transpose_smul, transpose_one, sub_left_inj]
    rw [isSymm_sum]
    intro k
    refine IsSymm.ext_iff.mpr (fun i j => CommMonoid.mul_comm ((ps k).act j) ((ps k).act i))


lemma patterns_pairwise_orthogonal (ps : Fin m → (HopfieldNetwork R U).State)
  (horth : ∀ {i j : Fin m} (_ : i ≠ j), dotProduct (ps i).act (ps j).act = 0) :
  ∀ (j : Fin m), ((Hebbian ps).w).mulVec (ps j).act = (card U - m) * (ps j).act := by
  intros k
  ext t
  unfold Hebbian
  rw [mulVec, dotProduct]
  simp only [sub_apply, smul_apply, smul_eq_mul, Pi.natCast_def, Pi.mul_apply, Pi.sub_apply]
  rw [Finset.sum_apply]
  simp only [Finset.sum_apply]
  unfold dotProduct at horth
  have : ∀ i j, (dotProduct (ps i).act (ps j).act) = if i ≠ j then 0 else card U := by
    intros i j
    by_cases h : i ≠ j
    · specialize horth h
      simp_all only [ne_eq, not_false_eq_true, reduceIte, Nat.cast_zero]
      assumption
    · simp only [Decidable.not_not] at h
      nth_rw 1 [h]
      simp only [ite_not, Nat.cast_ite, Nat.cast_zero]
      refine eq_ite_iff.mpr ?_
      left
      constructor
      · assumption
      · unfold dotProduct
        have hact : ∀ i, ((ps j).act i) = 1 ∨  ((ps j).act i) = -1 := fun i => act_one_or_neg_one i
        have hact1 : ∀ i, ((ps j).act i) * ((ps j).act i) = 1 := fun i => mul_self_eq_one_iff.mpr (hact i)
        calc _ = ∑ i, (ps j).act i * (ps j).act i := rfl
             _ = ∑ i, 1 * 1 := by simp_rw [hact1]; rw [mul_one]
             _ = card U := by simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  simp only [dotProduct, ite_not, Nat.cast_ite, Nat.cast_zero] at this
  conv => enter [1,2]; ext l; rw [sub_mul]; rw [sum_mul]; conv => enter [1,2]; ext i; rw [mul_assoc]
  rw [Finset.sum_sub_distrib]
  nth_rw 1 [sum_comm]
  calc _= ∑ y : Fin m, (ps y).act t * ∑ x , ((ps y).act x * (ps k).act x)
          - ∑ x , ↑m * (1 : Matrix U U R) t x * (ps k).act x := ?_
       _= ∑ y : Fin m, (ps y).act t *  (if y ≠ k then 0 else card U) -
            ∑ x , ↑m * (1 : Matrix U U R) t x * (ps k).act x := ?_
       _ = (card U - ↑m) * (ps k).act t  := ?_
  · simp only [sub_left_inj]; rw [Finset.sum_congr rfl]
    exact fun x _ => (mul_sum univ (fun i => (ps x).act i * (ps k).act i) ((ps x).act t)).symm
  · simp only [sub_left_inj]; rw [Finset.sum_congr rfl]; intros i _
    simp_all only [reduceIte, implies_true, mem_univ, mul_ite, mul_zero, ite_not, Nat.cast_ite, Nat.cast_zero]
  · simp only [ite_not, Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, Finset.sum_ite_eq', mem_univ, reduceIte]
    conv => enter [1,2,2]; ext k; rw [mul_assoc]
    rw [← mul_sum, mul_comm]
    simp only [one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, mem_univ, reduceIte]
    exact (sub_mul (card U : R) m ((ps k).act t)).symm

lemma stateisStablecondition (ps : Fin m → (HopfieldNetwork R U).State)
  (s : (HopfieldNetwork R U).State) c (hc : 0 < c)
  (hw : ∀ u, ((Hebbian ps).w).mulVec s.act u = c * s.act u) : s.isStable (Hebbian ps) := by
  intros u
  unfold Up out
  simp only [reduceIte, Fin.isValue]
  rw [HNfnet_eq]
  simp_rw [mulVec, dotProduct] at hw u
  refine ite_eq_iff.mpr ?_
  cases' s.act_one_or_neg_one u with h1 h2
  · left; rw [h1]; constructor
    · rw [hw, le_iff_lt_or_eq]; left; rwa [h1, mul_one]
    · rfl
  · right; rw [h2]; constructor
    · change ¬ 0 ≤ _
      rw [le_iff_lt_or_eq]
      simp only [not_or, not_lt]
      constructor
      · rw [le_iff_lt_or_eq]; left;
        simpa only [hw, h2, mul_neg, mul_one, Left.neg_neg_iff]
      · simp_all only [mul_neg, mul_one, zero_eq_neg]
        exact ne_of_gt hc
    · rfl
  exact (Hebbian ps).hw u u fun a => a rfl

lemma Hebbian_stable_orthogonal (hm : m < card U) (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m)
    (horth : ∀ {i j : Fin m} (_ : i ≠ j), dotProduct (ps i).act (ps j).act = 0):
  isStable (Hebbian ps) (ps j) := by
  unfold isStable
  have := patterns_pairwise_orthogonal ps horth j
  have hmn0 : 0 < (card U - m : R) := by
    simpa only [sub_pos, Nat.cast_lt]
  apply stateisStablecondition ps (ps j) (card U - m) hmn0
  · intros u; rw [funext_iff] at this; exact this u

lemma dotProduct_act_self (s : (HopfieldNetwork R U).State) :
  dotProduct s.act s.act = card U := by
  unfold dotProduct
  have hsq : ∀ u, s.act u * s.act u = 1 := by
    intro u
    have h := s.act_one_or_neg_one u
    cases h with
    | inl h1 => simp only [h1, mul_one]
    | inr h2 => simp only [h2, mul_neg, mul_one, neg_neg]
  simp_rw [hsq]
  simp [sum_const, card_univ, nsmul_eq_mul]

/- Disturbance term for non-orthogonal patterns. -/
def disturbance (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m) : (U → R) :=
fun u => ∑ i : Fin m, if i ≠ j then (ps i).act u * dotProduct (ps i).act (ps j).act else 0

/-- Full perturbed Hopfield update -/
def Wpj_perturbed (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m) : (U → R) :=
fun u => (card U - m : R) * (ps j).act u + disturbance ps j u

def neuron_update_perturbed (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m) : (U → R) :=
fun u => HNfact 0 (Wpj_perturbed ps j u)

set_option maxHeartbeats 2000000 in
lemma patterns_general (ps : Fin m → (HopfieldNetwork R U).State) (j : Fin m) :
  ((Hebbian ps).w).mulVec (ps j).act =
    (card U - m : R) • (ps j).act + disturbance ps j := by
  ext t
  -- Abbreviation for the `j`-th pattern.
  let pj : U → R := (ps j).act
  -- Expand the Hebbian field at coordinate `t`.
  have h_field : ((Hebbian ps).w).mulVec pj t =
    (∑ i : Fin m, (ps i).act t * dotProduct (ps i).act pj) - (m : R) * pj t := by
    unfold Hebbian
    have hsub :
        ((∑ i : Fin m, outerProduct (ps i) (ps i) - (m : R) • (1 : Matrix U U R)).mulVec pj) =
          (∑ i : Fin m, outerProduct (ps i) (ps i)).mulVec pj - ((m : R) • (1 : Matrix U U R)).mulVec pj := by
      simpa [Matrix.mulVec] using
        (sub_mulVec (A := (∑ i : Fin m, outerProduct (ps i) (ps i)))
          (B := (m : R) • (1 : Matrix U U R)) (x := pj))
    have hsub_t := congrArg (fun v => v t) hsub
    -- (i) the outer-product sum gives `∑ i, (ps i).act t * dotProduct (ps i).act pj`.
    have h_outer :
        ((∑ i : Fin m, outerProduct (ps i) (ps i)).mulVec pj) t =
          ∑ i : Fin m, (ps i).act t * dotProduct (ps i).act pj := by
      rw [mulVec, dotProduct]
      rw [Finset.sum_apply]
      have hentry (x : U) :
          (∑ i : Fin m, outerProduct (ps i) (ps i) t x) =
            ∑ i : Fin m, (ps i).act t * (ps i).act x := by
        simp [outerProduct]
      simp [hentry, dotProduct]
      have hdist :
          (∑ x : U, (∑ i : Fin m, (ps i).act t * (ps i).act x) * pj x) =
            ∑ x : U, ∑ i : Fin m, ((ps i).act t * (ps i).act x) * pj x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simpa [mul_assoc] using
          (Finset.sum_mul (s := (Finset.univ : Finset (Fin m)))
            (f := fun i : Fin m => (ps i).act t * (ps i).act x) (a := pj x))
      calc
        (∑ x : U, (∑ i : Fin m, (ps i).act t * (ps i).act x) * pj x)
            = ∑ x : U, ∑ i : Fin m, ((ps i).act t * (ps i).act x) * pj x := hdist
        _ = ∑ i : Fin m, ∑ x : U, ((ps i).act t * (ps i).act x) * pj x := by
              exact Finset.sum_comm
        _ = ∑ i : Fin m, (ps i).act t * ∑ x : U, (ps i).act x * pj x := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              have hreassoc :
                  (∑ x : U, ((ps i).act t * (ps i).act x) * pj x) =
                    ∑ x : U, (ps i).act t * ((ps i).act x * pj x) := by
                refine Finset.sum_congr rfl (fun x _ => ?_)
                ring_nf
              rw [hreassoc]
              simpa [dotProduct, mul_assoc] using
                (mul_sum (s := (Finset.univ : Finset U))
                  (f := fun x : U => (ps i).act x * pj x) ((ps i).act t)).symm
        _ = ∑ i : Fin m, (ps i).act t * dotProduct (ps i).act pj := by
              simp [dotProduct]
    -- (ii) the diagonal correction gives `m * pj t`.
    have h_diag : (((m : R) • (1 : Matrix U U R)).mulVec pj) t = (m : R) * pj t := by
      have hsmul :
          ((m : R) • (1 : Matrix U U R)).mulVec pj = (m : R) • ((1 : Matrix U U R).mulVec pj) := by
        simpa [Matrix.mulVec] using
          (smul_mulVec (b := (m : R)) (M := (1 : Matrix U U R)) (v := pj))
      have hone : ((1 : Matrix U U R).mulVec pj) = pj := by
        simp
      simp [hsmul, hone, Pi.smul_apply, smul_eq_mul]
    simpa [pj, Pi.sub_apply, h_outer, h_diag] using hsub_t
  -- Split the “signal” term `i = j` from the interference `i ≠ j`.
  set f : Fin m → R := fun i => (ps i).act t * dotProduct (ps i).act pj
  have h_self : dotProduct pj pj = card U := by
    simpa [pj] using (dotProduct_act_self (s := ps j))
  have h_split :
      (∑ i : Fin m, f i) = f j + ∑ i ∈ (Finset.univ.erase j), f i := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin m))) (a := j) (f := f)).symm
  have h_filter :
      (∑ i ∈ (Finset.univ.erase j), f i) = ∑ i : Fin m, if i ≠ j then f i else 0 := by
    simpa [filter_erase_equiv] using
      (Finset.sum_filter (s := (Finset.univ : Finset (Fin m))) (p := fun i => i ≠ j) (f := f))
  have h_sig_int :
      (∑ i : Fin m, f i) - (m : R) * pj t =
        ((card U - m : R) * pj t) + (∑ i : Fin m, if i ≠ j then f i else 0) := by
    calc
      (∑ i : Fin m, f i) - (m : R) * pj t
          = (f j + ∑ i ∈ (Finset.univ.erase j), f i) - (m : R) * pj t := by simp
      _ = (pj t * (card U : R) + ∑ i ∈ (Finset.univ.erase j), f i) - (m : R) * pj t := by
            simp [f, h_self, pj]
      _ = ((card U - m : R) * pj t) + ∑ i ∈ (Finset.univ.erase j), f i := by
            ring_nf
      _ = ((card U - m : R) * pj t) + (∑ i : Fin m, if i ≠ j then f i else 0) := by
            simp [h_filter]
  simp [h_field, h_sig_int, f, pj, disturbance, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
