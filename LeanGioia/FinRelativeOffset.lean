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

The proof passes through `ZMod N`, where subtraction is genuine modular
subtraction. The only case split is the canonical representative split:
whether the representative of `a + d` lies before or after `b`.

`omega` cannot see through `% N` for a variable `N`, so modular facts
are supplied explicitly and `omega` is used only after the relevant
quotient/remainder identities have been exposed.
-/

namespace LeanGioia

/--
A `Fin N` value, cast to `ZMod N`, has the same canonical representative.
-/
theorem zmod_val_of_fin
    {N : Nat} [NeZero N] (a : Fin N) :
    (a.val : ZMod N).val = a.val := by
  exact ZMod.val_natCast_of_lt a.2

/--
The value of a sum of two `Fin N` values agrees with the value of the
corresponding sum in `ZMod N`.
-/
theorem zmod_fin_add_val
    {N : Nat} [NeZero N] (a d : Fin N) :
    ((a.val : ZMod N) + (d.val : ZMod N)).val =
      (a + d).val := by
  rw [ZMod.val_add]
  rw [zmod_val_of_fin a]
  rw [zmod_val_of_fin d]
  rfl

/--
The `ZMod N` representative of `a + d - b` agrees with the `Fin N`
representative of the same modular expression.
-/
theorem zmod_fin_add_sub_val
    {N : Nat} [NeZero N] (a b d : Fin N) :
    ((a.val : ZMod N) + (d.val : ZMod N) - (b.val : ZMod N)).val =
      (a + d - b).val := by
  have hadd :
      ((a.val : ZMod N) + (d.val : ZMod N)).val =
        (a + d).val :=
    zmod_fin_add_val a d

  by_cases h :
      b.val ≤ (a + d).val

  · have hb :
        (b.val : ZMod N).val = b.val :=
      zmod_val_of_fin b

    have hz :
        ((b.val : ZMod N).val) ≤
          ((a.val : ZMod N) + (d.val : ZMod N)).val := by
      rw [hb, hadd]
      exact h

    rw [ZMod.val_sub hz]
    rw [hadd, hb]
    rw [Fin.val_sub]

    have hadN :
        (a + d).val < N :=
      (a + d).2

    have hsum :
        N - b.val + (a + d).val =
          N + ((a + d).val - b.val) := by
      omega

    have hlt :
        (a + d).val - b.val < N := by
      omega

    rw [hsum, Nat.add_mod_left]
    exact (Nat.mod_eq_of_lt hlt).symm

  · have hlt :
        (a + d).val < b.val := by
      omega

    have hb :
        (b.val : ZMod N).val = b.val :=
      zmod_val_of_fin b

    have hb0 :
        (b.val : ZMod N) ≠ 0 := by
      intro hz
      have hzval := congrArg ZMod.val hz
      rw [hb, ZMod.val_zero] at hzval
      omega

    have hneg :
        (-(b.val : ZMod N)).val =
          N - b.val := by
      haveI : NeZero (b.val : ZMod N) := ⟨hb0⟩
      simpa [hb] using
        (ZMod.val_neg_of_ne_zero (b.val : ZMod N))

    rw [sub_eq_add_neg]
    rw [ZMod.val_add]
    rw [hadd, hneg]
    rw [Fin.val_sub]
    rw [Nat.add_comm (a + d).val (N - b.val)]

/--
The explicit natural-number residue used by `relativeOverlapOffset`
is the canonical representative of the corresponding `ZMod N`
expression.
-/
theorem zmod_relativeOverlapOffset_val
    {N : Nat} [NeZero N] (a b d : Fin N) :
    ((a.val : ZMod N) + (d.val : ZMod N) - (b.val : ZMod N)).val =
      relativeOverlapOffset N a.val b.val d.val := by
  unfold relativeOverlapOffset

  have hadd :
      ((a.val : ZMod N) + (d.val : ZMod N)).val =
        (a + d).val :=
    zmod_fin_add_val a d

  have hb :
      (b.val : ZMod N).val = b.val :=
    zmod_val_of_fin b

  by_cases h :
      b.val ≤ (a + d).val

  · have hz :
        (b.val : ZMod N).val ≤
          ((a.val : ZMod N) + (d.val : ZMod N)).val := by
      rw [hb, hadd]
      exact h

    rw [ZMod.val_sub hz]
    rw [hadd, hb]

    have haddVal :
        (a + d).val =
          (a.val + d.val) % N := by
      rfl

    rw [haddVal]

    have hRb :
        b.val ≤ (a.val + d.val) % N := by
      simpa [haddVal] using h

    have hdm :
        N * ((a.val + d.val) / N) +
            (a.val + d.val) % N =
          a.val + d.val :=
      Nat.div_add_mod (a.val + d.val) N

    have hRlt :
        (a.val + d.val) % N < N :=
      Nat.mod_lt _ (NeZero.pos N)

    have hsum :
        a.val + d.val =
          N * ((a.val + d.val) / N) +
            (a.val + d.val) % N := by
      exact hdm.symm

    have hsub :
        a.val + d.val - b.val =
          N * ((a.val + d.val) / N) +
            ((a.val + d.val) % N - b.val) := by
      rw [hsum]
      omega

    have hab :
        b.val ≤ a.val + d.val := by
      exact hRb.trans (Nat.mod_le (a.val + d.val) N)

    have step1 :
        a.val + N + d.val - b.val =
          ((a.val + d.val) % N - b.val) +
            N * (((a.val + d.val) / N) + 1) := by
      have hleft :
          a.val + N + d.val - b.val =
            (a.val + d.val - b.val) + N := by
        omega
      rw [hleft, hsub]
      omega

    have hlt2 :
        (a.val + d.val) % N - b.val < N := by
      omega

    rw [step1, Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt hlt2).symm

  · have hlt :
        (a + d).val < b.val := by
      omega

    have hb0 :
        (b.val : ZMod N) ≠ 0 := by
      intro hz
      have hzval := congrArg ZMod.val hz
      rw [hb, ZMod.val_zero] at hzval
      omega

    have hneg :
        (-(b.val : ZMod N)).val =
          N - b.val := by
      haveI : NeZero (b.val : ZMod N) := ⟨hb0⟩
      simpa [hb] using
        (ZMod.val_neg_of_ne_zero (b.val : ZMod N))

    rw [sub_eq_add_neg]
    rw [ZMod.val_add]
    rw [hadd, hneg]

    have haddVal :
        (a + d).val =
          (a.val + d.val) % N := by
      rfl

    rw [haddVal]

    have hRb :
        (a.val + d.val) % N < b.val := by
      simpa [haddVal] using hlt

    have hbN :
        b.val < N :=
      b.2

    have hdm :
        N * ((a.val + d.val) / N) +
            (a.val + d.val) % N =
          a.val + d.val :=
      Nat.div_add_mod (a.val + d.val) N

    have hsum :
        a.val + d.val =
          N * ((a.val + d.val) / N) +
            (a.val + d.val) % N := by
      exact hdm.symm

    have step1 :
        a.val + N + d.val - b.val =
          ((a.val + d.val) % N + (N - b.val)) +
            N * ((a.val + d.val) / N) := by
      rw [hsum]
      omega

    rw [step1, Nat.add_mul_mod_self_left]

/--
The value of `a + d - b : Fin N` agrees with the explicit
natural-number cyclic residue used by `relativeOverlapOffset`.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by
  have hN : NeZero N :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt a.2)⟩
  letI : NeZero N := hN

  calc
    (a + d - b).val =
        ((a.val : ZMod N) +
          (d.val : ZMod N) -
          (b.val : ZMod N)).val := by
      symm
      exact zmod_fin_add_sub_val a b d
    _ =
        relativeOverlapOffset N a.val b.val d.val := by
      exact zmod_relativeOverlapOffset_val a b d

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
