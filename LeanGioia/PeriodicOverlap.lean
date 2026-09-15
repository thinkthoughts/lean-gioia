import LeanGioia.FinRelativeOffset
import LeanGioia.PeriodicRange

/-!
# LeanGioia.PeriodicOverlap

Checkpoint 32: connect the closed canonical relative-offset geometry
from Checkpoint 31 to the explicit cyclic blocks introduced in
Checkpoint 23.

Checkpoint 31 closed the representation bridge between the relative
offset expression and arithmetic in `Fin N`.  The resulting theorem
`canonicalOverlapInThreeRRegion_closed` says that canonical overlap
coordinates place a point `x` in the forward-or-backward region

`cyclicOffset N start x < 2 * R`

or

`N - R ≤ cyclicOffset N start x`.

This checkpoint supplies those canonical coordinates directly from
periodic overlap data.

If a shared point belongs to both range-`R` cyclic blocks and `x`
belongs to the competing block, then the three cyclic offsets required
by `CanonicalOverlapCoordinates` are all below `R`.  The closed
Checkpoint-31 theorem therefore places `x` in `InThreeRCoverRegion`.

The second theorem packages the shared point existentially, matching
the form obtained from a nonempty intersection of two cyclic blocks.

Thus CP32 closes the passage

periodic block overlap
→ canonical overlap coordinates
→ forward-or-backward `3R` region.
-/

namespace LeanGioia

/--
A concrete shared point of two cyclic range-`R` blocks supplies
canonical overlap coordinates and hence places `x` in the
forward-or-backward `3R` region.
-/
theorem canonical_overlap_coordinate_of_shared
    {N R : Nat}
    (hNR : 3 * R < N)
    {start competitorStart shared x : Fin N}
    (hSharedStart :
      shared ∈ cyclicBlock N R start)
    (hSharedCompetitor :
      shared ∈ cyclicBlock N R competitorStart)
    (hXCompetitor :
      x ∈ cyclicBlock N R competitorStart) :
    InThreeRCoverRegion R start x := by

  have hRleN : R ≤ N := by
    omega

  have hStart :
      cyclicOffset N start shared < R :=
    cyclicOffset_lt_of_mem_cyclicBlock
      hRleN
      hSharedStart

  have hCompetitorShared :
      cyclicOffset N competitorStart shared < R :=
    cyclicOffset_lt_of_mem_cyclicBlock
      hRleN
      hSharedCompetitor

  have hCompetitorX :
      cyclicOffset N competitorStart x < R :=
    cyclicOffset_lt_of_mem_cyclicBlock
      hRleN
      hXCompetitor

  have hcoords :
      CanonicalOverlapCoordinates N R start x :=
    { competitorStart := competitorStart
      shared := shared
      shared_from_selected_lt := hStart
      shared_from_competitor_lt := hCompetitorShared
      x_from_competitor_lt := hCompetitorX }

  exact
    canonicalOverlapInThreeRRegion_closed hNR
      start x hcoords

/--
Checkpoint-32 coordinate theorem with the shared point packaged as an
existential witness.

A nonempty intersection of the selected and competing range-`R`
cyclic blocks supplies a shared point.  Every point `x` in the
competing block then lies in the canonical forward-or-backward
`3R` region relative to the selected start.
-/
theorem canonical_overlap_coordinate_of_intersection_witness
    {N R : Nat}
    (hNR : 3 * R < N)
    {start competitorStart x : Fin N}
    (hShared :
      ∃ shared : Fin N,
        shared ∈ cyclicBlock N R start ∧
        shared ∈ cyclicBlock N R competitorStart)
    (hXCompetitor :
      x ∈ cyclicBlock N R competitorStart) :
    InThreeRCoverRegion R start x := by

  rcases hShared with
    ⟨shared, hSharedStart, hSharedCompetitor⟩

  exact
    canonical_overlap_coordinate_of_shared
      hNR
      hSharedStart
      hSharedCompetitor
      hXCompetitor

end LeanGioia
