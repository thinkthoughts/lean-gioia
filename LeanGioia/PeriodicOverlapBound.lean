import LeanGioia.PeriodicOverlap

/-!
# LeanGioia.PeriodicOverlapBound

Checkpoint 25: quantitative `3R` cover for the exact periodic overlap hull.

Checkpoint 24 removed the abstract overlap-localization field by defining
the exact overlap hull `overlapInteraction`.

To bound that hull, this checkpoint introduces an explicit cover consisting
of two pieces:

* the `2R` sites beginning at the selected start;
* an `R`-site cyclic block immediately preceding the selected start.

This cover has cardinality at most `3R`, purely by finite-set counting.
Consequently, any proof that the exact overlap hull is contained in this
cover immediately gives the desired `< N` bound from `3R < N`.

The remaining modular-arithmetic statement is isolated as one theorem
premise rather than mixed into the cardinality argument.
-/

namespace LeanGioia

/--
Move `back` sites backwards from `start` on the periodic chain.
-/
def cyclicBackStart
    (N back : Nat) (start : Fin N) : Fin N :=
  ⟨(start.1 + N - (back % N)) % N, by
    have hstart : start.1 < N := start.2
    have hN : 0 < N := by
      omega
    exact Nat.mod_lt _ hN⟩

/--
A concrete cover for every range-`R` block that can overlap the selected
range-`R` block.

The first piece covers the selected block and all overlap extending to its
right.  The second piece covers overlap extending to its left.
-/
def threeRInteractionCover
    (N R : Nat) (selectedStart : Fin N) : Finset (Fin N) :=
  cyclicBlock N (2 * R) selectedStart ∪
    cyclicBlock N R (cyclicBackStart N R selectedStart)

/--
The explicit interaction cover has cardinality at most `3R`.
-/
theorem threeRInteractionCover_card_le
    (N R : Nat) (selectedStart : Fin N) :
    (threeRInteractionCover N R selectedStart).card ≤ 3 * R := by
  unfold threeRInteractionCover
  calc
    (cyclicBlock N (2 * R) selectedStart ∪
        cyclicBlock N R (cyclicBackStart N R selectedStart)).card
        ≤ (cyclicBlock N (2 * R) selectedStart).card +
          (cyclicBlock N R (cyclicBackStart N R selectedStart)).card :=
      Finset.card_union_le _ _
    _ ≤ (2 * R) + R := by
      exact Nat.add_le_add
        (cyclicBlock_card_le N (2 * R) selectedStart)
        (cyclicBlock_card_le N R
          (cyclicBackStart N R selectedStart))
    _ = 3 * R := by
      omega

/--
Any subset of the explicit `3R` cover has cardinality at most `3R`.
-/
theorem card_le_three_mul_of_subset_cover
    {N R : Nat} {selectedStart : Fin N}
    {S : Finset (Fin N)}
    (hsub :
      S ⊆ threeRInteractionCover N R selectedStart) :
    S.card ≤ 3 * R := by
  exact le_trans
    (Finset.card_le_card hsub)
    (threeRInteractionCover_card_le N R selectedStart)

/--
Once the exact overlap hull is contained in the explicit cover, the
paper-scale hypothesis `3R < N` gives the required strict cardinality
bound.
-/
theorem overlapInteraction_card_lt_of_subset_threeR
    {N R : Nat} {selectedStart : Fin N}
    (hNR : 3 * R < N)
    (hsub :
      overlapInteraction N R selectedStart ⊆
        threeRInteractionCover N R selectedStart) :
    (overlapInteraction N R selectedStart).card < N := by
  have hle :
      (overlapInteraction N R selectedStart).card ≤ 3 * R :=
    card_le_three_mul_of_subset_cover hsub
  omega

/--
A periodic-overlap creation model can therefore be built from creator
support containment plus the single modular containment statement that the
exact overlap hull lies in the explicit `3R` cover.
-/
noncomputable def periodicOverlapModel_of_threeR_cover
    {N R : Nat} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (start : ι → Fin N)
    (hcreators :
      ∀ i : ι,
        (creators i).toFinset ⊆ cyclicBlock N R (start i))
    (hNR : 3 * R < N)
    (hcover :
      ∀ i : ι,
        overlapInteraction N R (start i) ⊆
          threeRInteractionCover N R (start i)) :
    PeriodicOverlapCreationModel N R ι creators where
  start := start

  creators_in_support := by
    intro i
    exact hcreators i

  interaction_card_lt := by
    intro i
    exact overlapInteraction_card_lt_of_subset_threeR
      hNR (hcover i)

/--
Checkpoint-25 end-to-end assembly.

The quantitative `3R < N` implication is now kernel-visible.  The only
remaining periodic-arithmetic statement is the set containment
`overlapInteraction ⊆ threeRInteractionCover`.
-/
theorem corollary_one_from_threeR_overlap_cover
    {N R : Nat} {ι κ : Type}
    [Fintype ι]
    [Fintype κ] [DecidableEq κ]
    (hN3 : 3 ≤ N)
    (hNR : 3 * R < N)
    (Ω : ℂ)
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (hnonid : NonidentityNormalOrderedFamily term)
    (singleCoeff : Fin N → ℂ)
    (singleEig : ℂ)
    (hSingleEig :
      IsEigenstate
        (singleCreationOperator singleCoeff)
        (wState N) singleEig)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (higherEig : ℂ)
    (hHigherEig :
      IsEigenstate
        (higherCreationFamilyOperator higherCoeff higherCreators)
        (wState N) higherEig)
    (hinj :
      Function.Injective
        (fun k : κ => (higherCreators k).toFinset))
    (start : κ → Fin N)
    (hcreators :
      ∀ k : κ,
        (higherCreators k).toFinset ⊆
          cyclicBlock N R (start k))
    (hcover :
      ∀ k : κ,
        overlapInteraction N R (start k) ⊆
          threeRInteractionCover N R (start k))
    (hatLeastTwo :
      ∀ k : κ,
        2 ≤ (higherCreators k).toFinset.card)
    (hNodup :
      ∀ k : κ,
        (higherCreators k).Nodup)
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by
  let M :
      PeriodicOverlapCreationModel N R κ higherCreators :=
    periodicOverlapModel_of_threeR_cover
      start hcreators hNR hcover

  exact corollary_one_from_periodicOverlap_creation_model
    hN3 Ω
    mixedCoeff term hnonid
    singleCoeff singleEig hSingleEig
    higherCoeff higherCreators higherEig hHigherEig
    hinj
    M
    hatLeastTwo hNodup
    hbridge

end LeanGioia
