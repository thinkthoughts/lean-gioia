import LeanGioia.Geometry

/-!
# LeanGioia.SupportWitness

Checkpoint 7: concrete finite-range support and higher-particle witness state.

Appendix C.1.a chooses a site `l` far from the contiguous support `A` of a
selected pure-creation term and considers the product configuration with
the sites in `A` occupied together with `l`.

This checkpoint connects the abstract `ExclusionRegion` from Checkpoint 6
to a concrete buffered support and constructs the corresponding basis-state
witness.  It proves that, for nonempty local support, the witness lies
outside the one-particle W sector.

The operator-amplitude statements needed to prove that the selected
pure-creation term is nonzero there and competing range-`R` terms vanish
are deliberately left to the next checkpoint.
-/

namespace LeanGioia

/--
A local support together with left and right buffer regions.

The paper's Appendix C separation argument only needs the total excluded
region to have size at most `3R`.  We record that by bounding each of the
three pieces by `R`.
-/
structure BufferedSupport (N R : ℕ) where
  core : Finset (Fin N)
  leftBuffer : Finset (Fin N)
  rightBuffer : Finset (Fin N)
  core_card_le : core.card ≤ R
  left_card_le : leftBuffer.card ≤ R
  right_card_le : rightBuffer.card ≤ R

/-- The full region excluded when selecting the distant witness site. -/
def BufferedSupport.excluded {N R : ℕ} (S : BufferedSupport N R) :
    Finset (Fin N) :=
  S.core ∪ S.leftBuffer ∪ S.rightBuffer

/-- The buffered support determines an `ExclusionRegion`. -/
def BufferedSupport.toExclusionRegion {N R : ℕ}
    (S : BufferedSupport N R) : ExclusionRegion N R where
  sites := S.excluded
  card_le := by
    dsimp [BufferedSupport.excluded]
    calc
      (S.core ∪ S.leftBuffer ∪ S.rightBuffer).card
          ≤ (S.core ∪ S.leftBuffer).card + S.rightBuffer.card :=
        Finset.card_union_le _ _
      _ ≤ (S.core.card + S.leftBuffer.card) + S.rightBuffer.card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ 3 * R := by
        omega

/--
Choose a site outside the concrete buffered support under the paper's
`N > 3R` size condition.
-/
noncomputable def BufferedSupport.chooseSeparated {N R : ℕ}
    (S : BufferedSupport N R) (hNR : 3 * R < N) :
    SeparatedSite N R S.toExclusionRegion :=
  chooseSeparatedSite S.toExclusionRegion hNR

/-- A separated site is outside the core local support. -/
theorem BufferedSupport.separated_not_mem_core {N R : ℕ}
    (S : BufferedSupport N R) (l : SeparatedSite N R S.toExclusionRegion) :
    l.site ∉ S.core := by
  intro hcore
  apply l.separated
  simp [IsSeparated, BufferedSupport.toExclusionRegion,
    BufferedSupport.excluded, hcore]

/-- Computational-basis configuration with exactly the sites in `s` occupied. -/
def occupiedBits {N : ℕ} (s : Finset (Fin N)) : Bitstring N :=
  fun j => decide (j ∈ s)

@[simp]
theorem occupiedBits_eq_true {N : ℕ} (s : Finset (Fin N)) (j : Fin N)
    (h : j ∈ s) :
    occupiedBits s j = true := by
  simp [occupiedBits, h]

@[simp]
theorem occupiedBits_eq_false {N : ℕ} (s : Finset (Fin N)) (j : Fin N)
    (h : j ∉ s) :
    occupiedBits s j = false := by
  simp [occupiedBits, h]

/--
The higher-particle basis configuration used as the Appendix C witness:
occupy every site in the selected core support and also the separated site.
-/
def BufferedSupport.witnessBits {N R : ℕ}
    (S : BufferedSupport N R)
    (l : SeparatedSite N R S.toExclusionRegion) :
    Bitstring N :=
  occupiedBits (insert l.site S.core)

@[simp]
theorem BufferedSupport.witness_site_occupied {N R : ℕ}
    (S : BufferedSupport N R)
    (l : SeparatedSite N R S.toExclusionRegion) :
    S.witnessBits l l.site = true := by
  simp [BufferedSupport.witnessBits, occupiedBits]

@[simp]
theorem BufferedSupport.witness_core_occupied {N R : ℕ}
    (S : BufferedSupport N R)
    (l : SeparatedSite N R S.toExclusionRegion)
    {j : Fin N} (hj : j ∈ S.core) :
    S.witnessBits l j = true := by
  simp [BufferedSupport.witnessBits, occupiedBits, hj]

/--
If the selected local support is nonempty, its witness configuration cannot
be any one-particle basis configuration: it contains a core excitation and
a distinct separated excitation.
-/
theorem BufferedSupport.witness_ne_singleExcitation {N R : ℕ}
    (S : BufferedSupport N R)
    (l : SeparatedSite N R S.toExclusionRegion)
    (hcore : S.core.Nonempty) (q : Fin N) :
    S.witnessBits l ≠ singleExcitationBits q := by
  obtain ⟨j, hj⟩ := hcore
  have hlj : l.site ≠ j := by
    intro h
    apply S.separated_not_mem_core l
    simpa [h] using hj
  intro heq
  by_cases hql : q = l.site
  · subst q
    have hAtJ := congrFun heq j
    have hwj : S.witnessBits l j = true :=
      S.witness_core_occupied l hj
    rw [hwj] at hAtJ
    simp [singleExcitationBits, hlj.symm] at hAtJ
  · have hAtL := congrFun heq l.site
    have hwl : S.witnessBits l l.site = true :=
      S.witness_site_occupied l
    rw [hwl] at hAtL
    simp [singleExcitationBits, hql] at hAtL

/--
The concrete higher-particle witness has zero W-state amplitude.
-/
theorem BufferedSupport.wState_witness_zero {N R : ℕ}
    (S : BufferedSupport N R)
    (l : SeparatedSite N R S.toExclusionRegion)
    (hcore : S.core.Nonempty) :
    wState N (S.witnessBits l) = 0 := by
  classical
  rw [wState_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro q hq
  apply basisState_apply_ne
  exact (S.witness_ne_singleExcitation l hcore q).symm

end LeanGioia
