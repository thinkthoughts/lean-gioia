/--
The cyclic block of `width` sites beginning at `start`.

Offsets are interpreted modulo `N`, so this definition passes through the
PBC link automatically.
-/
def cyclicBlock (N width : ℕ) (start : Fin N) : Finset (Fin N) :=
  (Finset.range width).image fun t =>
    (⟨(start.1 + t) % N, by
      have hN : 0 < N := by
        omega
      exact Nat.mod_lt _ hN⟩ : Fin N)

/--
Every cyclic block has cardinality at most its requested width.
No injectivity assumption is needed for this upper bound.
-/
theorem cyclicBlock_card_le
    (N width : ℕ) (start : Fin N) :
    (cyclicBlock N width start).card ≤ width := by
  unfold cyclicBlock
  calc
    ((Finset.range width).image
      (fun t =>
        (⟨(start.1 + t) % N, by
          have hN : 0 < N := by
            omega
          exact Nat.mod_lt _ hN⟩ : Fin N))).card
        ≤ (Finset.range width).card := Finset.card_image_le
    _ = width := by
      simp

/--
Membership form of an explicit cyclic block.
-/
theorem mem_cyclicBlock_iff
    {N width : ℕ} {start x : Fin N} :
    x ∈ cyclicBlock N width start ↔
      ∃ t < width, x.1 = (start.1 + t) % N := by
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, htx⟩
    refine ⟨t, ?_, ?_⟩
    · simpa using ht
    · have hval := congrArg Fin.val htx
      simpa using hval.symm
  · rintro ⟨t, ht, hval⟩
    apply Finset.mem_image.mpr
    refine ⟨t, ?_, ?_⟩
    · simpa using ht
    · apply Fin.ext
      simpa using hval.symm

/--
Concrete periodic range-`R` support data.

`start i` gives the left endpoint of the selected cyclic range block.

The only geometric fact kept as a specification here is the standard
overlap-localization statement: every competing range-`R` block that
overlaps the selected block lies inside the selected `3R` interaction
block.

Checkpoint 23 proves that this specification is enough to discharge the
cardinality condition from `3R < N`; the modular interval proof of
`overlap_localizes` is isolated as the next geometry lemma.
-/
structure PeriodicRangeCreationModel
    (N R : ℕ) (ι : Type) [Fintype ι]
    (creators : ι → List (Fin N)) where
  start : ι → Fin N

  creators_in_support :
    ∀ i : ι,
      (creators i).toFinset ⊆ cyclicBlock N R (start i)

  selected_in_interaction :
    ∀ i : ι,
      cyclicBlock N R (start i) ⊆ cyclicBlock N (3 * R) (start i)

  overlap_localizes :
    ∀ i k : ι,
      ¬ Disjoint
        (cyclicBlock N R (start k))
        (cyclicBlock N R (start i)) →
      cyclicBlock N R (start k) ⊆
        cyclicBlock N (3 * R) (start i)

/--
The explicit periodic `3R` interaction block is smaller than the full
chain whenever `3R < N`.
-/
theorem periodic_interaction_card_lt
    {N R : ℕ} (hNR : 3 * R < N) (start : Fin N) :
    (cyclicBlock N (3 * R) start).card < N := by
  have hle :
      (cyclicBlock N (3 * R) start).card ≤ 3 * R :=
    cyclicBlock_card_le N (3 * R) start
  omega

/--
A periodic range model with `3R < N` canonically supplies the abstract
finite-range model from Checkpoint 22.
-/
noncomputable def PeriodicRangeCreationModel.toFiniteRange
    {N R : ℕ} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : PeriodicRangeCreationModel N R ι creators)
    (hNR : 3 * R < N) :
    FiniteRangeCreationModel N ι creators where
  support := fun i => cyclicBlock N R (M.start i)
  interaction := fun i => cyclicBlock N (3 * R) (M.start i)

  creators_subset := by
    intro i
    exact M.creators_in_support i

  selected_subset_interaction := by
    intro i
    exact M.selected_in_interaction i

  overlap_support_subset_interaction := by
    intro i k hoverlap
    exact M.overlap_localizes i k hoverlap

  interaction_card_lt := by
    intro i
    exact periodic_interaction_card_lt hNR (M.start i)

/--
The periodic range model therefore generates all higher-creation witness
data automatically.
-/
noncomputable def all_higherCreationWitnessData_of_periodicRange
    {N R : ℕ} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : PeriodicRangeCreationModel N R ι creators)
    (hNR : 3 * R < N)
    (hatLeastTwo :
      ∀ i : ι, 2 ≤ (creators i).toFinset.card)
    (hNodup :
      ∀ i : ι, (creators i).Nodup) :
    ∀ i : ι, HigherCreationWitnessData creators i :=
  all_higherCreationWitnessData_of_finiteRange
    (M.toFiniteRange hNR) hatLeastTwo hNodup

/--
Checkpoint-23 end-to-end Corollary-1 theorem using periodic range data.

The former abstract `interaction_card_lt` premise has disappeared and is
now derived from the paper-scale hypothesis `3 * R < N`.
-/
theorem corollary_one_from_periodicRange_creation_model
    {N R : ℕ} {ι κ : Type}
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
    (M : PeriodicRangeCreationModel N R κ higherCreators)
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
  exact corollary_one_from_finiteRange_creation_model
    hN3 Ω
    mixedCoeff term hnonid
    singleCoeff singleEig hSingleEig
    higherCoeff higherCreators higherEig hHigherEig
    hinj
    (M.toFiniteRange hNR)
    hatLeastTwo hNodup
    hbridge

end LeanGioia
