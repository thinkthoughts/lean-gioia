import LeanGioia.PureCreationBridge

/-!
# LeanGioia.RangeLocality

Checkpoint 22: derive `HigherCreationWitnessData` from one explicit
finite-range/local-support model.

The source Appendix C.1.a assumes that every pure-creation term is
supported inside a contiguous range-`R` region and chooses a site `l`
sufficiently far from the selected support.  Any competing range-`R` term
that contains `l` is then disjoint from the selected support.

This file isolates exactly that geometry in a reusable finite support
structure.  Rather than supplying `HigherCreationWitnessData` separately
for every coefficient, we give:

* a support region for every term;
* creator sites contained in that support;
* a finite interaction neighborhood for each selected support;
* every competing support that meets the selected support lies inside that
  interaction neighborhood;
* the interaction neighborhood has cardinality `< N`.

Lean then chooses a witness site outside that neighborhood and derives the
locality condition required by Checkpoints 14--17.
-/

namespace LeanGioia

/--
Finite-range support data for a family of higher pure-creation terms.

`interaction i` represents the finite neighborhood that contains every
competing support capable of overlapping the support of term `i`.
For a one-dimensional range-`R` model this is the combinatorial object
corresponding to the `O(R)` region around the selected local block.
-/
structure FiniteRangeCreationModel
    (N : ℕ) (ι : Type) [Fintype ι]
    (creators : ι → List (Fin N)) where
  support : ι → Finset (Fin N)
  interaction : ι → Finset (Fin N)

  creators_subset :
    ∀ i : ι, (creators i).toFinset ⊆ support i

  selected_subset_interaction :
    ∀ i : ι, support i ⊆ interaction i

  overlap_support_subset_interaction :
    ∀ i k : ι,
      ¬ Disjoint (support k) (support i) →
      support k ⊆ interaction i

  interaction_card_lt :
    ∀ i : ι, (interaction i).card < N

/--
Every selected interaction neighborhood leaves at least one site available
outside it.
-/
theorem finiteRange_exists_witness_outside_interaction
    {N : ℕ} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : FiniteRangeCreationModel N ι creators)
    (i : ι) :
    ∃ l : Fin N, l ∉ M.interaction i := by
  classical
  exact exists_site_outside_of_card_lt
    (M.interaction i) (M.interaction_card_lt i)

/--
A witness chosen outside the selected interaction neighborhood is outside
the selected creator list.
-/
theorem finiteRange_witness_outside_creators
    {N : ℕ} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : FiniteRangeCreationModel N ι creators)
    {i : ι} {l : Fin N}
    (hl : l ∉ M.interaction i) :
    l ∉ creators i := by
  intro hlcre
  have hlin : l ∈ (creators i).toFinset := by
    simpa using hlcre
  have hlsupp : l ∈ M.support i :=
    M.creators_subset i hlin
  have hlinter : l ∈ M.interaction i :=
    M.selected_subset_interaction i hlsupp
  exact hl hlinter

/--
The finite-range support model implies the exact locality consequence used
in Checkpoint 14.

If a competing creator set contains the distant witness `l`, then it is
disjoint from the selected creator set.
-/
theorem finiteRange_separatedLocalCompetitor
    {N : ℕ} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : FiniteRangeCreationModel N ι creators)
    {i k : ι} {l : Fin N}
    (hl : l ∉ M.interaction i) :
    SeparatedLocalCompetitor
      (creators i).toFinset l (creators k).toFinset := by
  intro hlk
  apply Finset.disjoint_left.mpr
  intro x hxk hxi
  have hxksupp : x ∈ M.support k :=
    M.creators_subset k hxk
  have hxisupp : x ∈ M.support i :=
    M.creators_subset i hxi
  have hoverlap : ¬ Disjoint (M.support k) (M.support i) := by
    intro hdis
    exact (Finset.disjoint_left.mp hdis) hxksupp hxisupp
  have hksub :
      M.support k ⊆ M.interaction i :=
    M.overlap_support_subset_interaction i k hoverlap
  have hlksupp : l ∈ M.support k :=
    M.creators_subset k hlk
  exact hl (hksub hlksupp)

/--
Construct the complete higher-creation witness data required by
Checkpoint 17 from finite-range support geometry.
-/
theorem higherCreationWitnessData_of_finiteRange
    {N : ℕ} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : FiniteRangeCreationModel N ι creators)
    (hatLeastTwo :
      ∀ i : ι, 2 ≤ (creators i).toFinset.card)
    (hNodup :
      ∀ i : ι, (creators i).Nodup)
    (i : ι) :
    HigherCreationWitnessData creators i := by
  classical
  obtain ⟨l, hl⟩ :=
    finiteRange_exists_witness_outside_interaction M i
  refine
    { witnessSite := l
      atLeastTwo := hatLeastTwo i
      nodup := hNodup i
      witnessOutside := ?_
      locality := ?_ }
  · exact finiteRange_witness_outside_creators M hl
  · intro k
    exact finiteRange_separatedLocalCompetitor M hl

/--
All higher-creation terms receive witness data uniformly from one
finite-range model.
-/
theorem all_higherCreationWitnessData_of_finiteRange
    {N : ℕ} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : FiniteRangeCreationModel N ι creators)
    (hatLeastTwo :
      ∀ i : ι, 2 ≤ (creators i).toFinset.card)
    (hNodup :
      ∀ i : ι, (creators i).Nodup) :
    ∀ i : ι, HigherCreationWitnessData creators i := by
  intro i
  exact higherCreationWitnessData_of_finiteRange
    M hatLeastTwo hNodup i

/--
Checkpoint-22 end-to-end Corollary-1 assembly with the per-term
`HigherCreationWitnessData` hypothesis removed.

The higher-creation locality data is now generated from one finite-range
support model.
-/
theorem corollary_one_from_finiteRange_creation_model
    {N : ℕ} {ι κ : Type}
    [Fintype ι]
    [Fintype κ] [DecidableEq κ]
    (hN3 : 3 ≤ N)
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
    (M : FiniteRangeCreationModel N κ higherCreators)
    (hatLeastTwo :
      ∀ k : κ, 2 ≤ (higherCreators k).toFinset.card)
    (hNodup :
      ∀ k : κ, (higherCreators k).Nodup)
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by
  have hwitness :
      ∀ k : κ, HigherCreationWitnessData higherCreators k :=
    all_higherCreationWitnessData_of_finiteRange
      M hatLeastTwo hNodup
  exact corollary_one_from_verified_pure_creation_sectors
    hN3 Ω
    mixedCoeff term hnonid
    singleCoeff singleEig hSingleEig
    higherCoeff higherCreators higherEig hHigherEig
    hinj hwitness hbridge

end LeanGioia
