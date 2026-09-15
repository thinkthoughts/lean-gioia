import LeanGioia.OffsetComposition

/-!
# LeanGioia.FinRelativeOffset

Checkpoint 31: close the representation bridge between `Fin N`
arithmetic and the natural-number residue expression used in
Checkpoint 29.

Checkpoint 30 proved cyclic-offset composition in `Fin N`.

The remaining representation statement identifies the value of

`a + d - b : Fin N`

with `relativeOverlapOffset`.

The only arithmetic issue is the difference between Lean's canonical
`Fin.val_sub` representation and the explicit natural-number cyclic
residue used in Checkpoint 29.
-/

namespace LeanGioia

/--
Normalize the natural-number representation of cyclic subtraction.

This is the representation bridge between `Fin.val_sub` and
`relativeOverlapOffset`.
-/
theorem finRelativeOffset_nat_bridge
    {N a b d : Nat}
    (hN : 0 < N)
    (ha : a < N)
    (hb : b < N)
    (hd : d < N) :
    (N - b + (a + d) % N) % N =
      (a + N + d - b) % N := by

  have hr_lt : (a + d) % N < N :=
    Nat.mod_lt _ hN

  by_cases hcarry : a + d < N

  · rw [Nat.mod_eq_of_lt hcarry]

    have hraw_lt : a + N + d - b < 2 * N := by
      omega

    by_cases hab : b ≤ a + d

    · have hleft :
          N - b + (a + d) =
            (a + d - b) + N := by
        omega

      have hright :
          a + N + d - b =
            (a + d - b) + N := by
        omega

      rw [hleft, hright]

    · have hab' : a + d < b := by
        omega

      have hleft :
          N - b + (a + d) =
            N - (b - (a + d)) := by
        omega

      have hright :
          a + N + d - b =
            N - (b - (a + d)) := by
        omega

      rw [hleft, hright]

  · have hNle : N ≤ a + d := by
      omega

    have hsum_lt : a + d < 2 * N := by
      omega

    have hmod :
        (a + d) % N = a + d - N := by
      rw [Nat.mod_eq_sub_mod hNle]
      have hlt : a + d - N < N := by
        omega
      exact Nat.mod_eq_of_lt hlt

    rw [hmod]

    have hr : a + d - N < N := by
      omega

    by_cases hab : b ≤ a + d - N

    · have hleft :
          N - b + (a + d - N) =
            a + d - b := by
        omega

      have hright :
          a + N + d - b =
            (a + d - b) + N := by
        omega

      rw [hleft, hright]

      have hsmall : a + d - b < N := by
        omega

      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt hsmall]

    · have hab' : a + d - N < b := by
        omega

      have hleft :
          N - b + (a + d - N) =
            a + d - b := by
        omega

      have hright :
          a + N + d - b =
            (a + d - b) + N := by
        omega

      rw [hleft, hright]

      have hsmall : a + d - b < N := by
        omega

      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt hsmall]

/--
The value of `a + d - b : Fin N` agrees with the explicit
natural-number cyclic residue.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by

  have hN : 0 < N := by
    omega

  unfold relativeOverlapOffset

  simp only [Fin.val_sub, Fin.val_add]

  exact finRelativeOffset_nat_bridge
    hN a.2 b.2 d.2

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
