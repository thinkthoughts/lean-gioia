import LeanGioia.OffsetComposition
import Mathlib.Data.ZMod.Basic

/-!
# LeanGioia.FinRelativeOffset

Checkpoint 31: close the representation bridge between `Fin N`
arithmetic and the natural-number residue expression used in
Checkpoint 29.

Checkpoint 30 proved cyclic-offset composition in `Fin N`.

The remaining representation statement identifies the value of

`a + d - b : Fin N`

with the explicit natural-number cyclic residue

`(a.val + N + d.val - b.val) % N`.

Rather than proving this by case-splitting on truncated subtraction in
`Nat`, this checkpoint passes through `ZMod N`, where subtraction is
genuine modular subtraction.

The resulting theorem discharges `FinRelativeOffsetValueBridge` without
changing the interface established in Checkpoint 30.
-/

namespace LeanGioia

/--
The canonical embedding of `Fin N` into `ZMod N` preserves the represented
natural value.
-/
theorem zmod_val_natCast_fin
    {N : Nat} [NeZero N] (a : Fin N) :
    (a.val : ZMod N).val = a.val := by
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt a.2

/--
The `ZMod N` expression corresponding to the periodic difference
`a + d - b` agrees with the natural-number expression used by
`relativeOverlapOffset`.
-/
theorem zmod_relativeOffset_val
    {N : Nat} [NeZero N]
    (a b d : Fin N) :
    ((a.val : ZMod N) + (d.val : ZMod N) - (b.val : ZMod N)).val =
      relativeOverlapOffset N a.val b.val d.val := by
  unfold relativeOverlapOffset

  have hN : 0 < N := NeZero.pos N

  apply ZMod.val_eq_val
  simp only [ZMod.natCast_val]

  push_cast
  ring

/--
The `Fin N` expression `a + d - b` and the corresponding `ZMod N`
expression represent the same residue.
-/
theorem fin_add_sub_val_eq_zmod_val
    {N : Nat} [NeZero N]
    (a b d : Fin N) :
    (a + d - b).val =
      ((a.val : ZMod N) + (d.val : ZMod N) - (b.val : ZMod N)).val := by
  apply ZMod.val_eq_val

  simp only [Fin.val_add, Fin.val_sub]

  push_cast
  ring

/--
The value of `a + d - b : Fin N` agrees with the explicit
natural-number cyclic residue used by `relativeOverlapOffset`.

The empty `Fin 0` case requires no separate branch: the existence of
`a : Fin N` supplies positivity of `N`, hence the required `NeZero N`
instance.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by
  let hN : NeZero N :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt a.2)⟩
  letI : NeZero N := hN

  calc
    (a + d - b).val
        =
      ((a.val : ZMod N) +
          (d.val : ZMod N) -
          (b.val : ZMod N)).val := by
            exact fin_add_sub_val_eq_zmod_val a b d
    _ =
      relativeOverlapOffset N a.val b.val d.val := by
        exact zmod_relativeOffset_val a b d

/--
Checkpoint 30's representation bridge now holds.
-/
theorem finRelativeOffsetValueBridge
    (N : Nat) :
    FinRelativeOffsetValueBridge N := by
  intro a b d
  exact fin_add_sub_val_eq_relativeOverlapOffset a b d

/--
The canonical offset-composition proposition is now closed.
-/
theorem canonicalOffsetComposition_closed
    (N R : Nat) :
    CanonicalOffsetComposition N R := by
  exact canonicalOffsetComposition_of_finBridge
    (finRelativeOffsetValueBridge N)

/--
Under `3R < N`, canonical overlap coordinates lie in the
forward-or-backward `3R` region.
-/
theorem canonicalOverlapInThreeRRegion_closed
    {N R : Nat}
    (hNR : 3 * R < N) :
    CanonicalOverlapInThreeRRegion N R := by
  exact canonicalOverlapInThreeRRegion_of_finBridge
    hNR
    (finRelativeOffsetValueBridge N)

end LeanGioia
