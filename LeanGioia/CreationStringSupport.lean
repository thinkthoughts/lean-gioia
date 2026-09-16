import LeanGioia.HigherCreationSupportFiber

/-!
# LeanGioia.CreationStringSupport

Checkpoint 48: prove that duplicate-free creation strings are determined by
their finite creator support.

CP47 introduced support fibers and aggregate coefficients, but deliberately
left open whether equal `List.toFinset` support identifies the corresponding
`creationString` operators.

CP48 closes that representation-semantics boundary.  The proof proceeds from
the concrete hard-core creation semantics:

1. updates at distinct sites commute;
2. creation operators at distinct sites commute;
3. adjacent distinct creators may be swapped in a creation string;
4. creation strings are invariant under permutations of duplicate-free lists;
5. duplicate-free lists with equal `toFinset` support therefore determine the
   same creation-string operator.

This checkpoint does not yet regroup `higherCreationFamilyOperator` by support
or remove the existing creator-support injectivity hypothesis.
-/

namespace LeanGioia

/--
Setting two distinct bit positions commutes.
-/
theorem setBit_comm
    {N : Nat}
    (b : Bitstring N)
    (j k : Fin N)
    (v w : Bool)
    (hjk : j ≠ k) :
    setBit (setBit b j v) k w =
      setBit (setBit b k w) j v := by
  exact Function.update_comm hjk v w b

/--
Setting site `j` leaves the value at a distinct site `k` unchanged.
-/
theorem setBit_apply_of_ne
    {N : Nat}
    (b : Bitstring N)
    (j k : Fin N)
    (v : Bool)
    (hjk : j ≠ k) :
    setBit b j v k = b k := by
  simp [setBit, Function.update_apply, hjk.symm]

/--
Hard-core creation operators at distinct sites commute.
-/
theorem createAt_comp_comm_of_ne
    {N : Nat}
    (j k : Fin N)
    (hjk : j ≠ k) :
    composeOperator (createAt j) (createAt k) =
      composeOperator (createAt k) (createAt j) := by
  ext ψ b
  by_cases hbj : b j = true
  · by_cases hbk : b k = true
    · have hkj : k ≠ j := Ne.symm hjk
      have hj_after_k :
          setBit b k false j = true := by
        simpa [setBit_apply_of_ne b k j false hkj] using hbj
      have hk_after_j :
          setBit b j false k = true := by
        simpa [setBit_apply_of_ne b j k false hjk] using hbk
      simp [composeOperator_apply, createAt, hbj, hbk,
        hj_after_k, hk_after_j, setBit_comm b j k false false hjk]
    · have hk_after_j :
          setBit b j false k ≠ true := by
        simpa [setBit_apply_of_ne b j k false hjk] using hbk
      simp [composeOperator_apply, createAt, hbj, hbk, hk_after_j]
  · by_cases hbk : b k = true
    · have hkj : k ≠ j := Ne.symm hjk
      have hj_after_k :
          setBit b k false j ≠ true := by
        simpa [setBit_apply_of_ne b k j false hkj] using hbj
      simp [composeOperator_apply, createAt, hbj, hbk, hj_after_k]
    · simp [composeOperator_apply, createAt, hbj, hbk]

/--
Associativity of the repository's operator composition.
-/
theorem composeOperator_assoc
    {N : Nat}
    (A B C : Operator N) :
    composeOperator A (composeOperator B C) =
      composeOperator (composeOperator A B) C := by
  rfl

/--
Swapping two distinct adjacent creator sites leaves the creation string
unchanged.
-/
theorem creationString_swap_adjacent
    {N : Nat}
    (j k : Fin N)
    (js : List (Fin N))
    (hjk : j ≠ k) :
    creationString (j :: k :: js) =
      creationString (k :: j :: js) := by
  simp only [creationString]
  rw [composeOperator_assoc, composeOperator_assoc]
  rw [createAt_comp_comm_of_ne j k hjk]

/--
A permutation of a duplicate-free creator list determines the same creation
string.
-/
theorem creationString_eq_of_perm_of_nodup
    {N : Nat}
    {xs ys : List (Fin N)}
    (hperm : xs.Perm ys)
    (hx : xs.Nodup) :
    creationString xs = creationString ys := by
  induction hperm with
  | nil =>
      rfl
  | @cons x l₁ l₂ hperm ih =>
      have htail : l₁.Nodup := (List.nodup_cons.mp hx).2
      simp only [creationString]
      rw [ih htail]
  | @swap x y l =>
      have hxy : x ≠ y := by
        exact (List.nodup_cons.mp hx).1
      exact (creationString_swap_adjacent x y l hxy).symm
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
      have hmid : l₂.Nodup := hx.perm h₁
      exact (ih₁ hx).trans (ih₂ hmid)

/--
Checkpoint-48 representation invariant.

Two duplicate-free creator lists with equal finite creator support determine
the same creation-string operator.
-/
theorem creationString_eq_of_toFinset_eq
    {N : Nat}
    {xs ys : List (Fin N)}
    (hx : xs.Nodup)
    (hy : ys.Nodup)
    (hsupport : xs.toFinset = ys.toFinset) :
    creationString xs = creationString ys := by
  have hperm : xs.Perm ys :=
    List.perm_of_nodup_nodup_toFinset_eq hx hy hsupport
  exact creationString_eq_of_perm_of_nodup hperm hx

end LeanGioia
