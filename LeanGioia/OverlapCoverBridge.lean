import LeanGioia.OverlapRegion
import LeanGioia.PeriodicOverlapContainment

/-!
# LeanGioia.OverlapCoverBridge

Checkpoint 34: convert the canonical forward-or-backward overlap region
into the explicit offset certificate used by the periodic-overlap
containment machinery.

Checkpoint 33 proved that every point of the exact overlap hull lies in
`InThreeRCoverRegion R start x`,
meaning that its canonical cyclic offset from `start` is either

* forward: `cyclicOffset N start x < 2 * R`, or
* backward: `N - R ≤ cyclicOffset N start x`.

The forward branch directly supplies `IsForwardOffset`.

For the backward branch, the canonical offset lies in the final `R`
positions of the periodic chain. Moving the block start backward by
`R` therefore gives an offset below `R` from
`cyclicBackStart N R start`.

This closes the representation bridge
`InThreeRCoverRegion → InThreeRCoverByOffset`
and, together with Checkpoint 33, discharges `OverlapOffsetBound`.
-/

namespace LeanGioia

/--
A canonical cyclic offset below `bound` gives the explicit forward
offset certificate used by `InThreeRCoverByOffset`.
-/
theorem isForwardOffset_of_cyclicOffset_lt
    {N bound : Nat}
    {start x : Fin N}
    (h : cyclicOffset N start x < bound) :
    IsForwardOffset start x bound := by
  refine ⟨cyclicOffset N start x, h, ?_⟩
  exact cyclicOffset_spec start x

/--
Under the paper-scale hypothesis, a canonical offset in the final
`R` positions of the periodic chain lies in the range-`R` block
beginning `R` sites behind `start`.
-/
theorem mem_backwardBlock_of_cyclicOffset_ge
    {N R : Nat}
    (hNR : 3 * R < N)
    {start x : Fin N}
    (hback : N - R ≤ cyclicOffset N start x) :
    x ∈ cyclicBlock N R (cyclicBackStart N R start) := by
  have hRltN : R < N := by
    omega

  have hRmod : R % N = R :=
    Nat.mod_eq_of_lt hRltN

  have hNpos : 0 < N := by
    omega

  have hofflt :
      cyclicOffset N start x < N :=
    cyclicOffset_lt start x

  let d :=
    cyclicOffset N start x - (N - R)

  have hd : d < R := by
    dsimp [d]
    omega

  apply mem_cyclicBlock_iff.mpr
  refine ⟨d, hd, ?_⟩

  have hxspec :
      x.1 =
        (start.1 + cyclicOffset N start x) % N :=
    cyclicOffset_spec start x

  rw [hxspec]

  have hoff :
      cyclicOffset N start x =
        (N - R) + d := by
    dsimp [d]
    omega

  rw [hoff]

  unfold cyclicBackStart
  simp only [hRmod]

  have hstart : start.1 < N := start.2

  have hdN : d < N := by
    omega

  have hmod :
      ((start.1 + N - R) % N + d) % N =
        (start.1 + (N - R) + d) % N := by
    have hbase :
        start.1 + N - R =
          start.1 + (N - R) := by
      omega
    rw [hbase]
    rw [Nat.add_mod]
    rw [Nat.mod_mod]
    rw [Nat.mod_eq_of_lt hdN]

  rw [hmod]

  congr 1
  omega

/--
The backward canonical-offset region gives the explicit strict backward
offset certificate used by the existing containment machinery.
-/
theorem isStrictBackwardOffset_of_cyclicOffset_ge
    {N R : Nat}
    (hNR : 3 * R < N)
    {start x : Fin N}
    (hback : N - R ≤ cyclicOffset N start x) :
    IsStrictBackwardOffset start x R := by
  have hx :
      x ∈ cyclicBlock N R (cyclicBackStart N R start) :=
    mem_backwardBlock_of_cyclicOffset_ge hNR hback

  have hRleN : R ≤ N := by
    omega

  have hoff :
      cyclicOffset N (cyclicBackStart N R start) x < R :=
    cyclicOffset_lt_of_mem_cyclicBlock hRleN hx

  refine
    ⟨cyclicOffset N (cyclicBackStart N R start) x,
      hoff, ?_⟩

  exact cyclicOffset_spec (cyclicBackStart N R start) x

/--
The canonical forward-or-backward region implies the explicit offset
certificate used by `threeRInteractionCover`.
-/
theorem inThreeRCoverByOffset_of_inThreeRCoverRegion
    {N R : Nat}
    (hNR : 3 * R < N)
    {start x : Fin N}
    (h : InThreeRCoverRegion R start x) :
    InThreeRCoverByOffset R start x := by
  unfold InThreeRCoverRegion at h
  unfold InThreeRCoverByOffset

  rcases h with hfwd | hbwd

  · left
    exact isForwardOffset_of_cyclicOffset_lt hfwd

  · right
    exact
      isStrictBackwardOffset_of_cyclicOffset_ge
        hNR hbwd

/--
Checkpoint-34 closure theorem.

Under `3 * R < N`, the exact overlap hull satisfies the offset bound
previously isolated as the remaining periodic arithmetic specification.
-/
theorem overlapOffsetBound_closed
    {N R : Nat}
    (hNR : 3 * R < N) :
    OverlapOffsetBound N R := by
  intro start x hx

  have hregion :
      InThreeRCoverRegion R start x :=
    overlap_mem_in_threeR_region hNR hx

  exact
    inThreeRCoverByOffset_of_inThreeRCoverRegion
      hNR hregion

/--
The exact overlap hull is therefore contained in the explicit `3R`
interaction cover with no remaining offset assumption.
-/
theorem overlapInteraction_subset_threeRInteractionCover_closed
    {N R : Nat}
    (hNR : 3 * R < N)
    (start : Fin N) :
    overlapInteraction N R start ⊆
      threeRInteractionCover N R start := by
  exact
    overlapInteraction_subset_threeRInteractionCover
      (overlapOffsetBound_closed hNR)
      start

/--
The closed periodic arithmetic gives the strict interaction-cardinality
bound required by the finite-range model.
-/
theorem overlapInteraction_card_lt_closed
    {N R : Nat}
    (hNR : 3 * R < N)
    (start : Fin N) :
    (overlapInteraction N R start).card < N := by
  exact
    overlapInteraction_card_lt_of_offsetBound
      hNR
      (overlapOffsetBound_closed hNR)
      start

end LeanGioia
