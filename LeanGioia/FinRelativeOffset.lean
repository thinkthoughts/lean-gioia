import LeanGioia.OffsetComposition

/-!
# LeanGioia.FinRelativeOffset

Checkpoint 31: close the representation bridge between `Fin N`
group arithmetic and the natural-number residue expression used in
Checkpoint 29.

Checkpoint 30 proved the group-level identity in `Fin N` and reduced the
remaining work to `FinRelativeOffsetValueBridge N`.

This file proves that bridge by normalizing the value of `a + d - b`
against the explicit natural-number representative

`(a.val + N + d.val - b.val) % N`.
-/

namespace LeanGioia

/--
The value of `a + d - b : Fin N` is the explicit natural-number residue
used by `relativeOverlapOffset`.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by
  have hN : 0 < N := by
    exact Nat.pos_of_lt a.2
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩

  unfold relativeOverlapOffset
  simp only [Fin.val_sub, Fin.val_add]

  have hadd :
      ((a.val + d.val) % N + N - b.val) % N =
        (a.val + d.val + N - b.val) % N := by
    omega

  have hcomm :
      a.val + d.val + N - b.val =
        a.val + N + d.val - b.val := by
    omega

  rw [hadd, hcomm]

/--
Checkpoint 30's representation bridge now holds.
-/
theorem finRelativeOffsetValueBridge
    (N : Nat) :
    FinRelativeOffsetValueBridge N := by
  intro a b d
  exact fin_add_sub_val_eq_relativeOverlapOffset a b d

/--
The natural-number canonical offset composition proposition is therefore
available with no remaining bridge hypothesis.
-/
theorem canonicalOffsetComposition_closed
    (N R : Nat) :
    CanonicalOffsetComposition N R := by
  exact canonicalOffsetComposition_of_finBridge
    (finRelativeOffsetValueBridge N)

/--
Under `3R < N`, canonical overlap coordinates lie in the
forward-or-backward `3R` region with no remaining arithmetic assumptions.
-/
theorem canonicalOverlapInThreeRRegion_closed
    {N R : Nat}
    (hNR : 3 * R < N) :
    CanonicalOverlapInThreeRRegion N R := by
  exact canonicalOverlapInThreeRRegion_of_finBridge
    hNR
    (finRelativeOffsetValueBridge N)

end LeanGioia
