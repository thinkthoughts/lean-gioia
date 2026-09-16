import LeanGioia.PureCreationSupport

/-!
# LeanGioia.PureCreationFamilySupport

Checkpoint 40: lift the structural higher-creation support condition from
individual creator lists to an indexed higher-creation family.

This is a hypothesis-reduction checkpoint, not a new end-to-end Corollary-1
assembly theorem.

Checkpoints 38 and 39 isolated the structural distinction between singleton
pure-creation terms and higher pure-creation terms, and related list length
to distinct creator support under `List.Nodup`.

The periodic-overlap model currently asks separately for

`∀ k, 2 ≤ (higherCreators k).toFinset.card`.

For a structurally classified higher family, that condition is redundant:
`2 ≤ (higherCreators k).length` together with `Nodup` supplies the required
finite-support cardinality at every family index.

This checkpoint packages that implication at family level.  It deliberately
leaves the higher-family index type, creator-set injectivity, eigenstate data,
and `PureCreationSectorBridge` unchanged; those belong to later representation
checkpoints.
-/

namespace LeanGioia

/--
Structural higher-creation support for an indexed family, expressed at the
list level before conversion to finite creator sets.
-/
def HigherCreationFamilyListSupport
    {N : Nat} {κ : Type}
    (higherCreators : κ → List (Fin N)) : Prop :=
  ∀ k : κ, 2 ≤ (higherCreators k).length

/--
A nodup higher-creation list with at least two entries has at least two
distinct creator sites.
-/
theorem higherCreation_toFinset_card_ge_two
    {N : Nat}
    {creators : List (Fin N)}
    (hlength : 2 ≤ creators.length)
    (hnodup : creators.Nodup) :
    2 ≤ creators.toFinset.card := by
  rw [List.toFinset_card_of_nodup hnodup]
  exact hlength

/--
Checkpoint-40 family-level hypothesis reduction.

The list-level structural support condition plus per-term `Nodup` derives the
`toFinset.card ≥ 2` hypothesis consumed by the existing periodic-overlap and
higher-creation witness machinery.
-/
theorem higherCreationFamily_toFinset_card_ge_two
    {N : Nat} {κ : Type}
    (higherCreators : κ → List (Fin N))
    (hsupport : HigherCreationFamilyListSupport higherCreators)
    (hnodup : ∀ k : κ, (higherCreators k).Nodup) :
    ∀ k : κ, 2 ≤ (higherCreators k).toFinset.card := by
  intro k
  exact higherCreation_toFinset_card_ge_two
    (hsupport k)
    (hnodup k)

end LeanGioia
