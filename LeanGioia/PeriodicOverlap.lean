import LeanGioia.FinRelativeOffset
import LeanGioia.PeriodicRange

/-!
# LeanGioia.PeriodicOverlap

Checkpoint 32: connect the closed canonical relative-offset geometry
from Checkpoint 31 to the explicit cyclic blocks introduced in
Checkpoint 23.

The central geometric statement is formulated at the coordinate level:
if a shared point belongs to both range-`R` cyclic blocks, and `x`
belongs to the competing block, then the canonical relative coordinate
of `x` lies in the forward-or-backward `3R` region supplied by
`canonicalOverlapInThreeRRegion_closed`.

This checkpoint deliberately keeps the final conversion from that
canonical coordinate region to the one-sided `cyclicBlock N (3 * R)`
containment separate.  The distinction matters on a periodic chain:
the canonical overlap theorem records both forward and backward
representatives, while `cyclicBlock` is oriented from its start point.

Thus CP32 closes the overlap-coordinate consequence of CP31 without
silently strengthening it to a one-sided block-containment theorem.
-/

namespace LeanGioia

/--
A concrete shared point of two cyclic range-`R` blocks supplies the
three offset bounds required by `CanonicalOverlapInThreeRRegion`.
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
    relativeOverlapOffset
        N
        (cyclicOffset N start shared)
        (cyclicOffset N competitorStart shared)
        (cyclicOffset N competitorStart x) < 3 * R ∨
      N - 3 * R <
        relativeOverlapOffset
          N
          (cyclicOffset N start shared)
          (cyclicOffset N competitorStart shared)
          (cyclicOffset N competitorStart x) := by
  have hStart :
      cyclicOffset N start shared < R :=
    cyclicOffset_lt_of_mem_cyclicBlock
      (Nat.le_of_lt (lt_of_le_of_lt
        (Nat.le_mul_of_pos_left R (by omega : 0 < 3))
        hNR))
      hSharedStart

  have hCompetitorShared :
      cyclicOffset N competitorStart shared < R :=
    cyclicOffset_lt_of_mem_cyclicBlock
      (Nat.le_of_lt (lt_of_le_of_lt
        (Nat.le_mul_of_pos_left R (by omega : 0 < 3))
        hNR))
      hSharedCompetitor

  have hCompetitorX :
      cyclicOffset N competitorStart x < R :=
    cyclicOffset_lt_of_mem_cyclicBlock
      (Nat.le_of_lt (lt_of_le_of_lt
        (Nat.le_mul_of_pos_left R (by omega : 0 < 3))
        hNR))
      hXCompetitor

  exact
    canonicalOverlapInThreeRRegion_closed hNR
      hStart hCompetitorShared hCompetitorX

/--
Checkpoint-32 coordinate theorem with the shared point packaged as an
existential witness.

This is the direct form produced from nonempty intersection data:
once `shared` is chosen from both cyclic supports, every point `x` in
the competing support has a canonical overlap coordinate in the
forward-or-backward `3R` region.
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
    ∃ shared : Fin N,
      shared ∈ cyclicBlock N R start ∧
      shared ∈ cyclicBlock N R competitorStart ∧
      (relativeOverlapOffset
          N
          (cyclicOffset N start shared)
          (cyclicOffset N competitorStart shared)
          (cyclicOffset N competitorStart x) < 3 * R ∨
        N - 3 * R <
          relativeOverlapOffset
            N
            (cyclicOffset N start shared)
            (cyclicOffset N competitorStart shared)
            (cyclicOffset N competitorStart x)) := by
  rcases hShared with ⟨shared, hSharedStart, hSharedCompetitor⟩
  refine ⟨shared, hSharedStart, hSharedCompetitor, ?_⟩
  exact
    canonical_overlap_coordinate_of_shared
      hNR
      hSharedStart
      hSharedCompetitor
      hXCompetitor

end LeanGioia
