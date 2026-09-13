import LeanGioia.Cancellation

/-!
# LeanGioia.Geometry

Checkpoint 6: the finite-range separation geometry used in Appendix C.1.a.

The source proof chooses an extra site far from the support of a selected
range-`R` pure-creation term. The paper notes that `N > 3R` is sufficient
for the separation arguments presented there.

This checkpoint isolates the finite combinatorial content needed for that
step: if the sites excluded by a range-`R` interaction and its two
range-`R` buffers occupy at most `3R` sites, then a periodic chain with
`N > 3R` contains a site outside that exclusion region.
-/

namespace LeanGioia

/-- Excluded sites associated with a range-`R` local contribution. -/
structure ExclusionRegion (N R : ℕ) where
  sites : Finset (Fin N)
  card_le : sites.card ≤ 3 * R

/-- A site is separated from an exclusion region when it lies outside it. -/
def IsSeparated {N R : ℕ} (X : ExclusionRegion N R) (l : Fin N) : Prop :=
  l ∉ X.sites

/--
A subset of `Fin N` with cardinality strictly less than `N` cannot contain
every site.
-/
theorem exists_site_outside_of_card_lt {N : ℕ} (s : Finset (Fin N))
    (hcard : s.card < N) :
    ∃ l : Fin N, l ∉ s := by
  by_contra h
  push Not at h
  have hs : s = Finset.univ := by
    ext l
    simp [h l]
  rw [hs] at hcard
  simp at hcard

/--
If the local support plus two buffers occupy at most `3R` sites and
`3R < N`, there is a witness site outside that region.
-/
theorem exists_separated_site {N R : ℕ}
    (X : ExclusionRegion N R) (hNR : 3 * R < N) :
    ∃ l : Fin N, IsSeparated X l := by
  have hcard : X.sites.card < N :=
    lt_of_le_of_lt X.card_le hNR
  simpa [IsSeparated] using exists_site_outside_of_card_lt X.sites hcard

/-- A chosen separated site packaged with its proof of separation. -/
structure SeparatedSite (N R : ℕ) (X : ExclusionRegion N R) where
  site : Fin N
  separated : IsSeparated X site

/--
Choose a separated site under the `N > 3R` condition.

Uses classical choice because the target is data, not a proposition.
-/
noncomputable def chooseSeparatedSite {N R : ℕ}
    (X : ExclusionRegion N R) (hNR : 3 * R < N) :
    SeparatedSite N R X :=
  let l := Classical.choose (exists_separated_site X hNR)
  ⟨l, Classical.choose_spec (exists_separated_site X hNR)⟩

/--
Set the chosen separated site to occupied in a computational-basis
configuration.
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
