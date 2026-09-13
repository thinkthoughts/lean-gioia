import LeanGioia.Cancellation

/-!
# LeanGioia.Geometry

Checkpoint 6: the finite-range separation geometry used in Appendix C.1.a.

The source proof chooses an extra site far from the support of a selected
range-`R` pure-creation term.  The paper notes that `N > 3R` is sufficient
for the separation arguments presented there.

This checkpoint isolates the finite combinatorial content needed for that
step: if the sites excluded by a range-`R` interaction and its two
range-`R` buffers occupy at most `3R` sites, then a periodic chain with
`N > 3R` contains a site outside that exclusion region.

The next checkpoint will connect this separated site to the operator
amplitudes needed to build an `UncancellableWitness`.
-/

namespace LeanGioia

/--
The finite set of sites excluded when choosing a witness site for a
range-`R` local contribution.

`sites` represents the local support together with the left/right buffer
regions needed by the Appendix C cancellation argument.  The geometry
specific to a concrete contiguous support is summarized by the bound
`sites.card ≤ 3 * R`.
-/
structure ExclusionRegion (N R : ℕ) where
  sites : Finset (Fin N)
  card_le : sites.card ≤ 3 * R

/-- A site is separated from an exclusion region when it lies outside it. -/
def IsSeparated {N R : ℕ} (X : ExclusionRegion N R) (l : Fin N) : Prop :=
  l ∉ X.sites

/--
Finite counting lemma: a subset of `Fin N` with cardinality strictly less
than `N` cannot contain every site.
-/
theorem exists_site_outside_of_card_lt {N : ℕ} (s : Finset (Fin N))
    (hcard : s.card < N) :
    ∃ l : Fin N, l ∉ s := by
  by_contra h
  push_neg at h
  have hs : s = Finset.univ := by
    ext l
    simp [h l]
  rw [hs] at hcard
  simp at hcard

/--
The separation existence statement corresponding to the paper's
`N > 3R` condition.

If the local support plus its two buffers occupy at most `3R` sites and
`3R < N`, there is a witness site outside that entire region.
-/
theorem exists_separated_site {N R : ℕ}
    (X : ExclusionRegion N R) (hNR : 3 * R < N) :
    ∃ l : Fin N, IsSeparated X l := by
  have hcard : X.sites.card < N :=
    lt_of_le_of_lt X.card_le hNR
  simpa [IsSeparated] using exists_site_outside_of_card_lt X.sites hcard

/--
Package a separated site together with the exclusion region from which it
is separated.  This is convenient for the amplitude construction in the
next checkpoint.
-/
structure SeparatedSite (N R : ℕ) (X : ExclusionRegion N R) where
  site : Fin N
  separated : IsSeparated X site

/-- Construct a packaged separated site under the `N > 3R` condition. -/
noncomputable def chooseSeparatedSite {N R : ℕ}
    (X : ExclusionRegion N R) (hNR : 3 * R < N) :
    SeparatedSite N R X := by
  classical
  obtain ⟨l, hl⟩ := exists_separated_site X hNR
  exact ⟨l, hl⟩

/--
Set the chosen separated site to occupied in a computational-basis
configuration.  This is the basis-state operation used to form the
higher-particle witness in Appendix C.
-/
def addSeparatedExcitation {N R : ℕ} {X : ExclusionRegion N R}
    (b : Bitstring N) (l : SeparatedSite N R X) : Bitstring N :=
  setBit b l.site true

@[simp]
theorem addSeparatedExcitation_occupied {N R : ℕ}
    {X : ExclusionRegion N R} (b : Bitstring N)
    (l : SeparatedSite N R X) :
    addSeparatedExcitation b l l.site = true := by
  simp [addSeparatedExcitation, setBit]

end LeanGioia
