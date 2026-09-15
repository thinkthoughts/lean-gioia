import LeanGioia.OffsetComposition

/-!
# LeanGioia.FinRelativeOffset

Checkpoint 31: close the representation bridge between `Fin N`
arithmetic and the natural-number residue expression used in
Checkpoint 29.

Checkpoint 30 proved the group-level cyclic-offset composition in `Fin N`
and reduced the remaining work to `FinRelativeOffsetValueBridge N`.

The value of `a + d - b : Fin N` is the residue obtained by adding `a`
and `d`, then subtracting `b`, modulo `N`.

The target expression

`relativeOverlapOffset N a.val b.val d.val`

encodes the same residue as

`(a.val + N + d.val - b.val) % N`.

This file proves that representation bridge and closes the canonical
offset-composition layer.
-/

namespace LeanGioia

/--
For values strictly below `N`, reducing the positive summand before a
modular subtraction gives the same residue as reducing only at the end.
-/
theorem mod_add_sub_mod_eq
    {N a b d : Nat}
    (hN : 0 < N)
    (hb : b < N) :
    (N - b + ((a + d) % N)) % N =
      (a + N + d - b) % N := by

  have hsplit :
      a + d = (a + d) % N + N * ((a + d) / N) := by
    omega

  have hNb : N - b > 0 := by
    omega

  have hrewrite :
      a + N + d - b =
        (N - b + ((a + d) % N)) +
          N * ((a + d) / N) := by
    omega

  rw [hrewrite]

  rw [Nat.add_mod]

  simp

/--
The value of `a + d - b : Fin N` agrees with the explicit natural-number
residue used by `relativeOverlapOffset`.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by

  have hN : 0 < N :=
    Nat.pos_of_ne_zero (by
      intro hN0
      subst N
      exact Fin.elim0 a)

  unfold relativeOverlapOffset

  rw [Fin.val_sub]
  rw [Fin.val_add]

  exact mod_add_sub_mod_eq
    hN
    b.2

/--
Checkpoint 30's representation bridge now holds.
-/
theorem finRelativeOffsetValueBridge
    (N : Nat) :
    FinRelativeOffsetValueBridge N := by
  intro a b d
  exact fin_add_sub_val_eq_relativeOverlapOffset
    a b d

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
