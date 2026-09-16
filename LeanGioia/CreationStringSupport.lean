import LeanGioia.HigherCreationSupportFiber

/-!
# LeanGioia.CreationStringSupport

Checkpoint 48: make the finite creator support of a duplicate-free creation
string into a proved representation invariant.

CP47 introduced fibers of higher-creation family indices having equal
`List.toFinset` support, but deliberately did not identify equal supports with
equal `creationString` operators.

CP48 closes exactly that representation-semantics boundary.  The proof route
is intentionally local:

1. creation operators at distinct sites commute;
2. `creationString` is invariant under permutation of a duplicate-free creator
   list;
3. duplicate-free lists with equal `toFinset` support therefore determine the
   same creation-string operator.

This checkpoint does not yet regroup `higherCreationFamilyOperator` by support
or remove the existing injectivity hypothesis from the coefficient-isolation
theorem.  Those are later assembly steps.
-/

namespace LeanGioia

/--
Creation operators at distinct sites commute.

This is the local semantic fact needed to make order irrelevant for a
duplicate-free creator list.
-/
theorem createAt_comp_comm_of_ne
    {N : Nat} (j k : Fin N) (hjk : j ≠ k) :
    composeOperator (createAt j) (createAt k) =
      composeOperator (createAt k) (createAt j) := by
  ext ψ b
  by_cases hbj : b j = true
  · by_cases hbk : b k = true
    · simp [composeOperator_apply, createAt, hbj, hbk, setBit, hjk]
    · simp [composeOperator_apply, createAt, hbj, hbk, setBit, hjk]
  · by_cases hbk : b k = true
    · simp [composeOperator_apply, createAt, hbj, hbk, setBit, hjk]
    · simp [composeOperator_apply, createAt, hbj, hbk, setBit, hjk]

/--
Swapping two distinct adjacent creator sites leaves the creation string
unchanged.
-/
theorem creationString_swap_adjacent
    {N : Nat} (j k : Fin N) (js : List (Fin N)) (hjk : j ≠ k) :
    creationString (j :: k :: js) =
      creationString (k :: j :: js) := by
  simp only [creationString]
  change
    composeOperator (createAt j)
        (composeOperator (createAt k) (creationString js)) =
      composeOperator (createAt k)
        (composeOperator (createAt j) (creationString js))
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
  rw [createAt_comp_comm_of_ne j k hjk]

/--
Permutation invariance for duplicate-free creator lists.

`Nodup` ensures that every adjacent swap required by the permutation exchanges
distinct sites, so the local commutation theorem applies.
-/
theorem creationString_eq_of_perm_of_nodup
    {N : Nat} {xs ys : List (Fin N)}
    (hperm : xs.Perm ys) (hx : xs.Nodup) :
    creationString xs = creationString ys := by
  induction hperm with
  | nil =>
      rfl
  | cons x hperm ih =>
      have htail : _.Nodup := (List.nodup_cons.mp hx).2
      simp only [creationString]
      rw [ih htail]
  | swap x y l =>
      have hxy : x ≠ y := by
        intro h
        subst y
        simpa using hx
      exact creationString_swap_adjacent x y l hxy
  | trans h₁ h₂ ih₁ ih₂ =>
      have hmid : _.Nodup := hx.perm h₁
      exact (ih₁ hx).trans (ih₂ hmid)

/--
CP48 representation invariant.

Two duplicate-free creator lists with the same finite creator support determine
the same creation-string operator.
-/
theorem creationString_eq_of_toFinset_eq
    {N : Nat} {xs ys : List (Fin N)}
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hsupport : xs.toFinset = ys.toFinset) :
    creationString xs = creationString ys := by
  have hperm : xs.Perm ys := by
    exact List.perm_of_nodup_nodup_toFinset_eq hx hy hsupport
  exact creationString_eq_of_perm_of_nodup hperm hx

end LeanGioia
