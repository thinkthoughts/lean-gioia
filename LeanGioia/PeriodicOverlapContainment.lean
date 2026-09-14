import LeanGioia.PeriodicOverlapBound

/-!
# LeanGioia.PeriodicOverlapContainment

Checkpoint 26: isolate the remaining PBC arithmetic as an explicit
offset certificate, and use it to prove the overlap-hull containment.

For a selected start `s`, every site `x` in a block overlapping the
selected range-`R` block has a cyclic offset from `s` of one of two forms:

* forward: `x = s + d (mod N)` with `d < 2R`;
* backward: `x` lies in the `R`-site cyclic block beginning at
  `cyclicBackStart N R s`.

Those are exactly the two pieces of `threeRInteractionCover`.

This file proves the cover membership from those offset certificates and
packages the only remaining modular-arithmetic fact as a proposition
`OverlapOffsetBound`. The operator/locality chain then depends only on
that one arithmetic statement.

The next checkpoint can prove `OverlapOffsetBound` directly from two
overlapping `cyclicBlock` memberships without touching any operator code.
-/

namespace LeanGioia

/--
Forward offset certificate from `start`.
-/
def IsForwardOffset
    {N : Nat} (start x : Fin N) (bound : Nat) : Prop :=
  ∃ d < bound, x.1 = (start.1 + d) % N

/--
A forward offset `< width` is exactly enough to prove membership in the
corresponding cyclic block.
-/
theorem mem_cyclicBlock_of_forwardOffset
    {N width : Nat} {start x : Fin N}
    (h : IsForwardOffset start x width) :
    x ∈ cyclicBlock N width start := by
  rcases h with ⟨d, hd, hx⟩
  exact mem_cyclicBlock_iff.mpr ⟨d, hd, hx⟩

/--
A backward-side certificate expressed directly relative to the beginning
of the backward `R` block used by `threeRInteractionCover`.
-/
def IsStrictBackwardOffset
    {N : Nat} (start x : Fin N) (R : Nat) : Prop :=
  ∃ d < R,
    x.1 =
      ((cyclicBackStart N R start).1 + d) % N

/--
A strict backward certificate places a site in the backward component of
the explicit `3R` cover.
-/
theorem mem_backwardBlock_of_strictBackwardOffset
    {N R : Nat} {start x : Fin N}
    (h : IsStrictBackwardOffset start x R) :
    x ∈ cyclicBlock N R (cyclicBackStart N R start) := by
  rcases h with ⟨d, hd, hx⟩
  exact mem_cyclicBlock_iff.mpr ⟨d, hd, hx⟩

/--
Arithmetic certificate sufficient for membership in the explicit
interaction cover.
-/
def InThreeRCoverByOffset
    {N : Nat} (R : Nat) (start x : Fin N) : Prop :=
  IsForwardOffset start x (2 * R) ∨
    IsStrictBackwardOffset start x R

/--
The offset certificate implies membership in the explicit `3R` cover.
-/
theorem mem_threeRInteractionCover_of_offset
    {N R : Nat} {start x : Fin N}
    (h : InThreeRCoverByOffset R start x) :
    x ∈ threeRInteractionCover N R start := by
  unfold InThreeRCoverByOffset at h
  unfold threeRInteractionCover
  rcases h with hfwd | hbwd
  · exact Finset.mem_union_left _
      (mem_cyclicBlock_of_forwardOffset hfwd)
  · exact Finset.mem_union_right _
      (mem_backwardBlock_of_strictBackwardOffset hbwd)

/--
The single remaining modular-arithmetic specification:

every site in the exact overlap hull admits either the forward `< 2R`
offset certificate or membership in the backward `R` component of the
explicit interaction cover.
-/
def OverlapOffsetBound (N R : Nat) : Prop :=
  ∀ (start x : Fin N),
    x ∈ overlapInteraction N R start →
      InThreeRCoverByOffset R start x

/--
`OverlapOffsetBound` implies the exact containment left open by
Checkpoint 25.
-/
theorem overlapInteraction_subset_threeRInteractionCover
    {N R : Nat}
    (hoffset : OverlapOffsetBound N R)
    (start : Fin N) :
    overlapInteraction N R start ⊆
      threeRInteractionCover N R start := by
  intro x hx
  exact mem_threeRInteractionCover_of_offset
    (hoffset start x hx)

/--
With `3R < N`, the offset theorem immediately gives the quantitative
cardinality bound for the exact overlap hull.
-/
theorem overlapInteraction_card_lt_of_offsetBound
    {N R : Nat}
    (hNR : 3 * R < N)
    (hoffset : OverlapOffsetBound N R)
    (start : Fin N) :
    (overlapInteraction N R start).card < N := by
  exact overlapInteraction_card_lt_of_subset_threeR
    hNR
    (overlapInteraction_subset_threeRInteractionCover
      hoffset start)

/--
Construct the periodic-overlap model directly from creator support and the
single global offset theorem.
-/
noncomputable def periodicOverlapModel_of_offsetBound
    {N R : Nat} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (start : ι → Fin N)
    (hcreators :
      ∀ i : ι,
        (creators i).toFinset ⊆ cyclicBlock N R (start i))
    (hNR : 3 * R < N)
    (hoffset : OverlapOffsetBound N R) :
    PeriodicOverlapCreationModel N R ι creators where
  start := start

  creators_in_support := by
    intro i
    exact hcreators i

  interaction_card_lt := by
    intro i
    exact overlapInteraction_card_lt_of_offsetBound
      hNR hoffset (start i)

/--
Checkpoint-26 end-to-end assembly.

All previous locality, witness, Table-I-Row-1, and Corollary-1 results now
depend on exactly one PBC arithmetic proposition: `OverlapOffsetBound`.
-/
theorem corollary_one_from_periodic_offset_bound
    {N R : Nat} {ι κ : Type}
    [Fintype ι]
    [Fintype κ] [DecidableEq κ]
    (hN3 : 3 ≤ N)
    (hNR : 3 * R < N)
    (hoffset : OverlapOffsetBound N R)
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
    periodicOverlapModel_of_offsetBound
      start hcreators hNR hoffset

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
