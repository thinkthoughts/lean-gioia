import LeanGioia.OffsetComposition

/-!
# LeanGioia.FinRelativeOffset

Checkpoint 31: close the representation bridge between `Fin N`
arithmetic and the natural-number residue expression used in
Checkpoint 29.

Checkpoint 30 proved cyclic-offset composition in `Fin N`.

The remaining representation statement identifies the value of

`a + d - b : Fin N`

with the explicit natural-number residue

`(a.val + d.val + N - b.val) % N`.

This is exactly the representation used by `relativeOverlapOffset`.
-/

namespace LeanGioia

/--
Adding a multiple of the modulus before taking `% N` leaves the
remainder unchanged.
-/
theorem add_modulus_mod
    {N u : Nat}
    (hN : 0 < N) :
    (u + N) % N = u % N := by
  rw [Nat.add_mod]
  simp [hN]

/--
Reducing the left summand modulo `N` before forming a cyclic subtraction
does not change the final residue.

This is the Nat-level normalization needed for the value formula of
subtraction in `Fin N`.
-/
theorem mod_add_modulus_sub_mod
    {N u b : Nat}
    (hN : 0 < N)
    (hb : b < N) :
    (u % N + N - b) % N =
      (u + N - b) % N := by
  have hu :
      u = u % N + N * (u / N) := by
    exact (Nat.mod_add_div u N).symm

  rw [hu]

  have hmodlt : u % N < N :=
    Nat.mod_lt u hN

  by_cases hbu : b ≤ u % N

  · have hleft :
        u % N + N - b =
          (u % N - b) + N := by
      omega

    have hright :
        u % N + N * (u / N) + N - b =
          (u % N - b) + N * ((u / N) + 1) := by
      omega

    rw [hleft, hright]

    have hsmall :
        u % N - b < N := by
      omega

    simp [Nat.add_mod, hN, hsmall]

  · have hbu' : u % N < b := by
      omega

    have hleft :
        u % N + N - b =
          N - (b - u % N) := by
      omega

    have hright :
        u % N + N * (u / N) + N - b =
          (N - (b - u % N)) +
            N * (u / N) := by
      omega

    rw [hleft, hright]

    have hdiff_pos :
        0 < b - u % N := by
      omega

    have hdiff_le :
        b - u % N ≤ N := by
      omega

    have hsmall :
        N - (b - u % N) < N := by
      omega

    simp [Nat.add_mod, hN, hsmall]

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

  have hb : b.val < N :=
    b.2

  unfold relativeOverlapOffset

  simp only [Fin.val_sub, Fin.val_add]

  have hnormalize :
      ((a.val + d.val) % N + N - b.val) % N =
        (a.val + d.val + N - b.val) % N := by
    exact mod_add_modulus_sub_mod hN hb

  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    hnormalize

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
