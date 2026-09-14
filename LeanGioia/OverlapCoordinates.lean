import LeanGioia.CyclicOffset

/-!
# LeanGioia.OverlapCoordinates

Checkpoint 28: extract canonical coordinates from a periodic overlap.

Checkpoint 27 normalized cyclic-block membership into inequalities for
`cyclicOffset`.  This checkpoint applies that normalization to the exact
overlap hull.

For any `x ∈ overlapInteraction N R start`, Lean now extracts:

* a competing range-`R` block start `c`;
* a shared site `y` witnessing that the selected and competing blocks
  overlap;
* the three canonical bounds

  `offset start y < R`,
  `offset c y < R`,
  `offset c x < R`.

This is the complete coordinate data needed for the final PBC inequality.
No operator, coefficient, or locality machinery remains in the next step.
-/

namespace LeanGioia

/--
Raw block-coordinate witness extracted directly from membership in the
exact overlap hull.
-/
structure OverlapCoordinateWitness
    (N R : Nat) (start x : Fin N) where
  competitorStart : Fin N
  shared : Fin N

  selectedOffset : Nat
  competitorSharedOffset : Nat
  competitorXOffset : Nat

  selectedOffset_lt :
    selectedOffset < R

  competitorSharedOffset_lt :
    competitorSharedOffset < R

  competitorXOffset_lt :
    competitorXOffset < R

  shared_from_selected :
    shared.1 =
      (start.1 + selectedOffset) % N

  shared_from_competitor :
    shared.1 =
      (competitorStart.1 + competitorSharedOffset) % N

  x_from_competitor :
    x.1 =
      (competitorStart.1 + competitorXOffset) % N

/--
Membership in the exact overlap hull supplies explicit finite block
coordinates.
-/
noncomputable def overlapCoordinateWitness_of_mem
    {N R : Nat} {start x : Fin N}
    (hx : x ∈ overlapInteraction N R start) :
    OverlapCoordinateWitness N R start x := by
  classical

  have hx' :
      ∃ competitorStart : Fin N,
        ¬ Disjoint
          (cyclicBlock N R competitorStart)
          (cyclicBlock N R start) ∧
        x ∈ cyclicBlock N R competitorStart := by
    simpa [overlapInteraction] using hx

  rcases hx' with ⟨c, hoverlap, hxc⟩

  have hcommon :
      ∃ y : Fin N,
        y ∈ cyclicBlock N R c ∧
        y ∈ cyclicBlock N R start := by
    exact Finset.not_disjoint_iff.mp hoverlap

  rcases hcommon with ⟨y, hyc, hys⟩

  rcases mem_cyclicBlock_iff.mp hys with
    ⟨a, ha, hya⟩

  rcases mem_cyclicBlock_iff.mp hyc with
    ⟨b, hb, hyb⟩

  rcases mem_cyclicBlock_iff.mp hxc with
    ⟨d, hd, hxd⟩

  exact
    { competitorStart := c
      shared := y
      selectedOffset := a
      competitorSharedOffset := b
      competitorXOffset := d
      selectedOffset_lt := ha
      competitorSharedOffset_lt := hb
      competitorXOffset_lt := hd
      shared_from_selected := hya
      shared_from_competitor := hyb
      x_from_competitor := hxd }

/--
Canonical-offset form of the overlap witness.

The actual offset values are no longer carried as arbitrary witnesses:
they are the canonical `cyclicOffset` values introduced in Checkpoint 27.
-/
structure CanonicalOverlapCoordinates
    (N R : Nat) (start x : Fin N) where
  competitorStart : Fin N
  shared : Fin N

  shared_from_selected_lt :
    cyclicOffset N start shared < R

  shared_from_competitor_lt :
    cyclicOffset N competitorStart shared < R

  x_from_competitor_lt :
    cyclicOffset N competitorStart x < R

/--
Under the paper-scale condition `3R < N`, every site in the overlap hull
has canonical overlap coordinates.

The only use of `3R < N` here is to obtain `R ≤ N`, which is the width
condition needed by the cyclic-block/offset equivalence.
-/
noncomputable def canonicalOverlapCoordinates_of_mem
    {N R : Nat} {start x : Fin N}
    (hNR : 3 * R < N)
    (hx : x ∈ overlapInteraction N R start) :
    CanonicalOverlapCoordinates N R start x := by
  classical

  have hRleN : R ≤ N := by
    omega

  have hx' :
      ∃ competitorStart : Fin N,
        ¬ Disjoint
          (cyclicBlock N R competitorStart)
          (cyclicBlock N R start) ∧
        x ∈ cyclicBlock N R competitorStart := by
    simpa [overlapInteraction] using hx

  rcases hx' with ⟨c, hoverlap, hxc⟩

  have hcommon :
      ∃ y : Fin N,
        y ∈ cyclicBlock N R c ∧
        y ∈ cyclicBlock N R start := by
    exact Finset.not_disjoint_iff.mp hoverlap

  rcases hcommon with ⟨y, hyc, hys⟩

  exact
    { competitorStart := c
      shared := y
      shared_from_selected_lt :=
        cyclicOffset_lt_of_mem_cyclicBlock hRleN hys
      shared_from_competitor_lt :=
        cyclicOffset_lt_of_mem_cyclicBlock hRleN hyc
      x_from_competitor_lt :=
        cyclicOffset_lt_of_mem_cyclicBlock hRleN hxc }

/--
Pointwise reduction of `OverlapOffsetBound`.

To prove the global bound, it is now enough to prove the following pure
cyclic-offset implication for the canonical coordinate data extracted
above.
-/
def CanonicalOverlapImpliesCover (N R : Nat) : Prop :=
  ∀ (start x : Fin N),
    CanonicalOverlapCoordinates N R start x →
      InThreeRCoverByOffset R start x

/--
The canonical offset implication discharges `OverlapOffsetBound`.
-/
theorem overlapOffsetBound_of_canonical
    {N R : Nat}
    (hNR : 3 * R < N)
    (hcanon : CanonicalOverlapImpliesCover N R) :
    OverlapOffsetBound N R := by
  intro start x hx
  exact hcanon start x
    (canonicalOverlapCoordinates_of_mem hNR hx)

end LeanGioia
