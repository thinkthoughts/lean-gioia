import LeanGioia.OverlapArithmetic

/-!
# LeanGioia.OffsetComposition

Checkpoint 30: prove the canonical cyclic-offset composition identity.

Checkpoint 29 reduced the remaining PBC geometry to one statement:
`CanonicalOffsetComposition`.

For canonical overlap coordinates with selected start `s`, competing start
`c`, shared point `y`, and target point `x`, define

* `a = cyclicOffset N s y`,
* `b = cyclicOffset N c y`,
* `d = cyclicOffset N c x`.

Then the clockwise offset from `s` to `x` is

`(a + N + d - b) mod N`.

This file proves that identity directly from `cyclicOffset_spec`.
-/

namespace LeanGioia

/--
A general composition identity for cyclic offsets through an intermediate
base point.

If `y` is reached from both `start` and `competitorStart`, then the offset
from `start` to `x` is obtained by adding the offset to `y`, subtracting
the competitor's offset to `y`, and adding the competitor's offset to `x`,
all modulo `N`.
-/
theorem cyclicOffset_compose_through_shared
    {N : Nat}
    (start competitorStart shared x : Fin N) :
    cyclicOffset N start x =
      relativeOverlapOffset N
        (cyclicOffset N start shared)
        (cyclicOffset N competitorStart shared)
        (cyclicOffset N competitorStart x) := by
  unfold relativeOverlapOffset
  unfold cyclicOffset

  have hstart : start.1 < N := start.2
  have hc : competitorStart.1 < N := competitorStart.2
  have hy : shared.1 < N := shared.2
  have hx : x.1 < N := x.2
  have hN : 0 < N := by
    omega

  have hsy := cyclicOffset_spec start shared
  have hcy := cyclicOffset_spec competitorStart shared
  have hcx := cyclicOffset_spec competitorStart x

  have hsy' :
      shared.1 =
        (start.1 + ((shared.1 + N - start.1) % N)) % N := by
    simpa [cyclicOffset] using hsy

  have hcy' :
      shared.1 =
        (competitorStart.1 +
          ((shared.1 + N - competitorStart.1) % N)) % N := by
    simpa [cyclicOffset] using hcy

  have hcx' :
      x.1 =
        (competitorStart.1 +
          ((x.1 + N - competitorStart.1) % N)) % N := by
    simpa [cyclicOffset] using hcx

  have hmodStart :
      ((x.1 + N - start.1) % N) =
        ((((shared.1 + N - start.1) % N) + N +
            ((x.1 + N - competitorStart.1) % N) -
            ((shared.1 + N - competitorStart.1) % N)) % N) := by

    have h1 :
        (start.1 +
            ((shared.1 + N - start.1) % N)) % N =
          shared.1 := by
      symm
      exact hsy'

    have h2 :
        (competitorStart.1 +
            ((shared.1 + N - competitorStart.1) % N)) % N =
          shared.1 := by
      symm
      exact hcy'

    have h3 :
        (competitorStart.1 +
            ((x.1 + N - competitorStart.1) % N)) % N =
          x.1 := by
      symm
      exact hcx'

    omega

  exact hmodStart

/--
The canonical composition proposition from Checkpoint 29 now holds
unconditionally.
-/
theorem canonicalOffsetComposition
    (N R : Nat) :
    CanonicalOffsetComposition N R := by
  intro start x h
  exact cyclicOffset_compose_through_shared
    start h.competitorStart h.shared x

/--
Canonical overlap coordinates therefore imply the forward-or-backward
`3R` region under `3R < N`.
-/
theorem canonicalOverlapInThreeRRegion
    {N R : Nat}
    (hNR : 3 * R < N) :
    CanonicalOverlapInThreeRRegion N R := by
  exact canonicalOverlapInThreeRRegion_of_composition
    hNR (canonicalOffsetComposition N R)

/--
The remaining `OverlapOffsetBound` proposition is discharged.
-/
theorem overlapOffsetBound
    {N R : Nat}
    (hNR : 3 * R < N) :
    OverlapOffsetBound N R := by
  exact overlapOffsetBound_of_canonical
    hNR
    (fun start x h =>
      canonicalOverlap_in_threeR_region
        hNR
        (canonicalOffsetComposition N R)
        start x h)

end LeanGioia
