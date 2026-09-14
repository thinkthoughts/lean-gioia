import LeanGioia.HigherCreation

/-!
# LeanGioia.HigherCreationUniqueness

Checkpoint 14: locality uniqueness for the `n ≥ 2, m = 0`
higher-particle witness.

Appendix C.1.a chooses a distant site `l` relative to the selected creator
support `A`.  A competing pure-creation term can contribute to the same
witness only if its creator set `B`, together with the single W-input site
`q`, reproduces the same occupied set:

`insert q B = insert l A`.

There are then two possibilities.

* If `l ∉ B`, the equality forces `q = l`, hence `B = A`.
* If `l ∈ B`, locality plus separation from `A` forbids `B` from also
  containing creator sites from `A`.  For `|A| ≥ 2`, one input site `q`
  cannot account for every site of `A`, so this case is impossible.

This file formalizes that finite-set uniqueness argument.  The next
checkpoint will connect nonzero operator amplitudes to these witness-set
representations and then invoke the cancellation lemma from Checkpoint 5.
-/

namespace LeanGioia

/--
A creator set `B` is local relative to a separated selected support `A`
and distant site `l` if any competing local term containing `l` contains
no site of `A`.

This is the exact locality consequence used by the combinatorial uniqueness
argument below.  Deriving it from a concrete periodic range-`R` metric is a
separate geometric layer.
-/
def SeparatedLocalCompetitor {N : ℕ}
    (A : Finset (Fin N)) (l : Fin N) (B : Finset (Fin N)) : Prop :=
  l ∈ B → Disjoint B A

/--
A competing pure-creation term with creator set `B` can reach the selected
higher-particle witness if there is a single W-input site `q` such that
occupying `B` together with `q` gives exactly the selected witness set
`A ∪ {l}`.
-/
def RepresentsHigherCreationWitness {N : ℕ}
    (A : Finset (Fin N)) (l q : Fin N) (B : Finset (Fin N)) : Prop :=
  insert q B = insert l A

/--
Locality uniqueness for the higher-particle witness.

If the selected creator support `A` contains at least two sites, `l` is
outside `A`, and a competing creator set `B` is local relative to the
separation of `l` from `A`, then any representation of the same witness
must use exactly the selected creator set `A`.
-/
theorem higherCreationWitness_creatorSet_unique {N : ℕ}
    (A B : Finset (Fin N)) (l q : Fin N)
    (hcard : 2 ≤ A.card)
    (hlA : l ∉ A)
    (hlocal : SeparatedLocalCompetitor A l B)
    (hrep : RepresentsHigherCreationWitness A l q B) :
    B = A := by
  classical
  unfold RepresentsHigherCreationWitness at hrep
  by_cases hlB : l ∈ B
  · have hdis : Disjoint B A := hlocal hlB
    have hAsub : A ⊆ ({q} : Finset (Fin N)) := by
      intro a haA
      have haRight : a ∈ insert l A := by
        simp [haA]
      have haLeft : a ∈ insert q B := by
        rw [hrep]
        exact haRight
      rcases Finset.mem_insert.mp haLeft with haq | haB
      · simp [haq]
      · exact False.elim ((Finset.disjoint_left.mp hdis) haB haA)
    have hcardle :
        A.card ≤ ({q} : Finset (Fin N)).card :=
      Finset.card_le_card hAsub
    simp at hcardle
    omega
  · have hlLeft : l ∈ insert q B := by
      rw [hrep]
      simp
    have hlq : l = q := by
      simpa [hlB] using hlLeft
    have hql : q = l := hlq.symm
    subst q
    ext a
    by_cases hal : a = l
    · subst a
      simp [hlA, hlB]
    · have hm :=
        congrArg (fun s : Finset (Fin N) => a ∈ s) hrep
      simpa [hal] using hm

/--
List-level form used by the operator-string representation.

Under the same locality/separation hypotheses, a competing duplicate-free
creator list that reaches the selected witness has the same creator set as
the selected list.
-/
theorem higherCreationWitness_creatorList_toFinset_unique {N : ℕ}
    (js ks : List (Fin N)) (l q : Fin N)
    (hcard : 2 ≤ js.toFinset.card)
    (hl : l ∉ js)
    (hlocal : SeparatedLocalCompetitor js.toFinset l ks.toFinset)
    (hrep :
      RepresentsHigherCreationWitness js.toFinset l q ks.toFinset) :
    ks.toFinset = js.toFinset := by
  apply higherCreationWitness_creatorSet_unique
    js.toFinset ks.toFinset l q hcard
  · simpa using hl
  · exact hlocal
  · exact hrep

end LeanGioia
