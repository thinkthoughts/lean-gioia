import LeanGioia.OverlapArithmetic

/-!
# LeanGioia.OffsetComposition

Checkpoint 30: prove cyclic-offset composition at the `Fin N` level.

Checkpoint 29 isolated the remaining PBC geometry as a composition of
three canonical cyclic offsets.

Trying to prove the corresponding equality directly between nested
natural-number `% N` expressions asks `omega` to solve modular arithmetic
that it is not designed to normalize.

This checkpoint instead moves the composition into `Fin N`, where addition
and subtraction already carry the periodic arithmetic.

For selected start `s`, competing start `c`, shared site `y`, and target
site `x`, the canonical offsets satisfy

`offset(s,x) = offset(s,y) + offset(c,x) - offset(c,y)`

as elements of `Fin N`.

That group-level statement is the mathematical core of
`CanonicalOffsetComposition`.

The remaining bridge is purely representational: identify the value of the
right-hand `Fin N` expression with the natural-number
`relativeOverlapOffset` from Checkpoint 29.
-/

namespace LeanGioia

/--
Package a canonical natural-number cyclic offset as an element of `Fin N`.
-/
def cyclicOffsetFin
    {N : Nat} (start x : Fin N) : Fin N :=
  ⟨cyclicOffset N start x, cyclicOffset_lt start x⟩

/--
Adding the canonical offset to its starting site recovers the target site
in `Fin N`.
-/
theorem start_add_cyclicOffsetFin
    {N : Nat} (start x : Fin N) :
    start + cyclicOffsetFin start x = x := by
  apply Fin.ext
  simpa [cyclicOffsetFin, Fin.val_add] using
    (cyclicOffset_spec start x).symm

/--
The canonical offset is therefore the group difference `x - start`.
-/
theorem cyclicOffsetFin_eq_sub
    {N : Nat} (start x : Fin N) :
    cyclicOffsetFin start x = x - start := by
  have h₁ :
      start + cyclicOffsetFin start x = x :=
    start_add_cyclicOffsetFin start x

  have h₂ :
      start + (x - start) = x := by
    abel

  exact add_left_cancel (h₁.trans h₂.symm)

/--
Cyclic offsets compose through a shared point.

This is the PBC composition identity expressed directly in the additive
group `Fin N`.
-/
theorem cyclicOffsetFin_compose_through_shared
    {N : Nat}
    (start competitorStart shared x : Fin N) :
    cyclicOffsetFin start x =
      cyclicOffsetFin start shared +
        cyclicOffsetFin competitorStart x -
          cyclicOffsetFin competitorStart shared := by
  rw [cyclicOffsetFin_eq_sub]
  rw [cyclicOffsetFin_eq_sub]
  rw [cyclicOffsetFin_eq_sub]
  rw [cyclicOffsetFin_eq_sub]
  abel

/--
The `Fin N` form of the canonical overlap composition proposition.
-/
def CanonicalFinOffsetComposition (N R : Nat) : Prop :=
  ∀ (start x : Fin N)
    (h : CanonicalOverlapCoordinates N R start x),
    cyclicOffsetFin start x =
      cyclicOffsetFin start h.shared +
        cyclicOffsetFin h.competitorStart x -
          cyclicOffsetFin h.competitorStart h.shared

/--
The `Fin N` canonical composition proposition holds without additional
range hypotheses.
-/
theorem canonicalFinOffsetComposition
    (N R : Nat) :
    CanonicalFinOffsetComposition N R := by
  intro start x h
  exact cyclicOffsetFin_compose_through_shared
    start h.competitorStart h.shared x

/--
The natural value of a packaged canonical offset is the original
`cyclicOffset`.
-/
@[simp]
theorem cyclicOffsetFin_val
    {N : Nat} (start x : Fin N) :
    (cyclicOffsetFin start x).val =
      cyclicOffset N start x := by
  rfl

/--
The remaining representation bridge between Checkpoint 30's group-level
composition and Checkpoint 29's natural-number expression.

This proposition states exactly that the value of

`a + d - b : Fin N`

agrees with the natural-number encoding

`(a.val + N + d.val - b.val) % N`.

Keeping this bridge explicit avoids mixing the group proof with the
Nat-truncation/modulo normalization.
-/
def FinRelativeOffsetValueBridge (N : Nat) : Prop :=
  ∀ a b d : Fin N,
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val

/--
Once the value bridge is available, the `Fin N` composition theorem
immediately yields Checkpoint 29's `CanonicalOffsetComposition`.
-/
theorem canonicalOffsetComposition_of_finBridge
    {N R : Nat}
    (hbridge : FinRelativeOffsetValueBridge N) :
    CanonicalOffsetComposition N R := by
  intro start x h

  have hfin :=
    cyclicOffsetFin_compose_through_shared
      start h.competitorStart h.shared x

  have hval := congrArg Fin.val hfin

  rw [cyclicOffsetFin_val] at hval

  have hbridge' :=
    hbridge
      (cyclicOffsetFin start h.shared)
      (cyclicOffsetFin h.competitorStart h.shared)
      (cyclicOffsetFin h.competitorStart x)

  rw [cyclicOffsetFin_val] at hbridge'
  rw [cyclicOffsetFin_val] at hbridge'
  rw [cyclicOffsetFin_val] at hbridge'

  calc
    cyclicOffset N start x
        =
      (cyclicOffsetFin start h.shared +
          cyclicOffsetFin h.competitorStart x -
          cyclicOffsetFin h.competitorStart h.shared).val := by
            exact hval
    _ =
      relativeOverlapOffset N
        (cyclicOffset N start h.shared)
        (cyclicOffset N h.competitorStart h.shared)
        (cyclicOffset N h.competitorStart x) := by
          exact hbridge'

/--
Consequently, the `3R` region theorem from Checkpoint 29 follows as soon
as the single Fin/Nat value bridge is established.
-/
theorem canonicalOverlapInThreeRRegion_of_finBridge
    {N R : Nat}
    (hNR : 3 * R < N)
    (hbridge : FinRelativeOffsetValueBridge N) :
    CanonicalOverlapInThreeRRegion N R := by
  exact canonicalOverlapInThreeRRegion_of_composition
    hNR
    (canonicalOffsetComposition_of_finBridge hbridge)

end LeanGioia
