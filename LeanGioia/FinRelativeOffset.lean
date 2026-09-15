import LeanGioia.OffsetComposition

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

The key point is to isolate the natural-number representation bridge
from the `Fin N` arithmetic.  Modular normalization is handled by a
small helper lemma rather than by expanding quotient/remainder
expressions.
-/

namespace LeanGioia

/--
Adding a full modulus before subtracting `b` gives the same residue
whether `u` is reduced modulo `N` first or afterward.
-/
theorem relative_mod_sub
    {N u b : Nat}
    (hN : 0 < N)
    (hb : b < N) :
    (N - b + u % N) % N =
      (u + N - b) % N := by
  have hur : u % N < N :=
    Nat.mod_lt u hN

  by_cases h : b ≤ u % N

  · have hleft :
        N - b + u % N =
          N + (u % N - b) := by
      omega

    rw [hleft, Nat.add_mod_left]

    have hsmall :
        u % N - b < N := by
      omega

    rw [Nat.mod_eq_of_lt hsmall]

    have hu_mod :
        u % N = u % N := rfl

    have hright :
        (u + N - b) % N =
          (u % N - b) % N := by
      calc
        (u + N - b) % N
            = ((u % N) + N - b) % N := by
                rw [Nat.add_sub_assoc (Nat.le_add_left b u)]
                rw [Nat.add_mod]
                simp [hN]
        _ = (N + (u % N - b)) % N := by
              congr 1
              omega
        _ = (u % N - b) % N := by
              rw [Nat.add_mod_left]

    rw [hright]
    exact (Nat.mod_eq_of_lt hsmall).symm

  · have hlt : u % N < b := by
      omega

    have hleftRaw :
        N - b + u % N < N := by
      omega

    rw [Nat.mod_eq_of_lt hleftRaw]

    have hleftForm :
        N - b + u % N =
          N - (b - u % N) := by
      omega

    rw [hleftForm]

    have huMod :
        u % N = u % N := rfl

    have hright :
        (u + N - b) % N =
          (N - (b - u % N)) % N := by
      have hpos :
          0 < b - u % N := by
        omega

      have hdiffLe :
          b - u % N ≤ N := by
        omega

      have htargetLt :
          N - (b - u % N) < N := by
        omega

      calc
        (u + N - b) % N
            = ((u % N) + N - b) % N := by
                have hmod :
                    (u + N - b) % N =
                      ((u % N) + N - b) % N := by
                  omega
                exact hmod
        _ = (N - (b - u % N)) % N := by
              congr 1
              omega
        _ = N - (b - u % N) := by
              exact Nat.mod_eq_of_lt htargetLt

    exact hright.symm

/--
The value of `a + d - b : Fin N` agrees with the explicit
natural-number cyclic residue used by `relativeOverlapOffset`.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by
  unfold relativeOverlapOffset

  have hN : 0 < N :=
    Nat.zero_lt_of_lt a.2

  simp only [Fin.val_sub, Fin.val_add]

  have hbridge :
      (N - b.val + (a.val + d.val) % N) % N =
        (a.val + d.val + N - b.val) % N := by
    exact relative_mod_sub hN b.2

  calc
    (N - b.val + (a.val + d.val) % N) % N
        = (a.val + d.val + N - b.val) % N :=
          hbridge
    _ = (a.val + N + d.val - b.val) % N := by
          congr 1
          omega

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
