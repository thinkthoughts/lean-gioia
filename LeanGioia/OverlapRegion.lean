import LeanGioia.PeriodicOverlap
import LeanGioia.OverlapInteraction

/-!
# LeanGioia.OverlapRegion

Checkpoint 33: lift the pointwise periodic-overlap coordinate theorem
from Checkpoint 32 to the exact periodic overlap hull.

Checkpoint 32 proved that a concrete shared point between the selected
range-`R` block and a competing range-`R` block supplies canonical
overlap coordinates and places every point of the competing block in

`InThreeRCoverRegion R start x`.

The exact overlap hull `overlapInteraction N R start` already records
precisely the existence of such a competing block together with
nonempty intersection and membership of `x` in that block.

This checkpoint therefore closes the global geometric statement:

`x ∈ overlapInteraction N R start`

implies

`InThreeRCoverRegion R start x`

under the paper-scale condition `3 * R < N`.

Equivalently, every point in the exact overlap hull has canonical
cyclic offset either

`cyclicOffset N start x < 2 * R`

or

`N - R ≤ cyclicOffset N start x`.

The remaining conversion from this canonical region statement to the
explicit forward/backward block certificate
`InThreeRCoverByOffset` is deliberately left as the next checkpoint.
-/

namespace LeanGioia

/--
The canonical region bound for the exact periodic overlap hull.
-/
def OverlapRegionBound (N R : Nat) : Prop :=
  ∀ (start x : Fin N),
    x ∈ overlapInteraction N R start →
      InThreeRCoverRegion R start x

/--
Under `3 * R < N`, every point in the exact periodic overlap hull lies
in the canonical forward-or-backward `3R` region.
-/
theorem overlapRegionBound_closed
    {N R : Nat}
    (hNR : 3 * R < N) :
    OverlapRegionBound N R := by
  intro start x hx

  have hcoords :
      CanonicalOverlapCoordinates N R start x :=
    canonicalOverlapCoordinates_of_mem hNR hx

  exact
    canonicalOverlapInThreeRRegion_closed hNR
      start x hcoords

/--
Pointwise form of the closed exact-overlap region theorem.
-/
theorem overlap_mem_in_threeR_region
    {N R : Nat}
    (hNR : 3 * R < N)
    {start x : Fin N}
    (hx : x ∈ overlapInteraction N R start) :
    InThreeRCoverRegion R start x := by
  exact
    overlapRegionBound_closed hNR
      start x hx

/--
Expanded form of the Checkpoint-33 conclusion.

Every point in the exact overlap hull has canonical cyclic offset
either in the forward interval below `2R` or in the backward interval
beginning at `N - R`.
-/
theorem overlap_mem_cyclicOffset_region
    {N R : Nat}
    (hNR : 3 * R < N)
    {start x : Fin N}
    (hx : x ∈ overlapInteraction N R start) :
    cyclicOffset N start x < 2 * R ∨
      N - R ≤ cyclicOffset N start x := by
  exact
    overlap_mem_in_threeR_region hNR hx

end LeanGioia
