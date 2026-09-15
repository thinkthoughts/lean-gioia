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

encodes the same cyclic residue as

`(a.val + N + d.val - b.val) % N`.

This file proves that representation bridge and closes the canonical
offset-composition layer.
-/

namespace LeanGioia

/--
Adding one full period before subtracting `b` gives the same residue as
modular subtraction.

This is the Nat-level representation lemma needed to connect `Fin N`
subtraction with `relativeOverlapOffset`.
-/
theorem mod_add_period_sub_eq
    {N u b : Nat}
    (hN : 0 < N)
    (hb : b < N) :
    ((u % N) + N - b) % N =
      (u + N - b) % N := by
  have hbN : b ≤ N := by
    omega

  have hmod :
      u % N < N :=
    Nat.mod_lt u hN

  by_cases hub : b ≤ u % N

  · have hleft :
        (u % N + N - b) % N =
          (u % N - b) % N := by
      have heq :
          u % N + N - b =
            (u % N - b) + N := by
        omega
      rw [heq, Nat.add_mod]
      simp

    have hright :
        (u + N - b) % N =
          (u % N - b) % N := by
      have heq :
          u + N - b =
            (u - b) + N := by
        omega
      rw [heq, Nat.add_mod]
      simp

      have hub' : b ≤ u := by
        exact le_trans hub (Nat.mod_le u N)

      have hsubmod :
          (u - b) % N =
            (u % N - b) % N := by
        exact Nat.sub_mod_eq_sub_mod hub

      exact hsubmod

    rw [hleft, hright]

  · have hbu : u % N < b := by
      omega

    have hleftRaw :
        u % N + N - b < N := by
      omega

    have hleft :
        (u % N + N - b) % N =
          u % N + N - b := by
      exact Nat.mod_eq_of_lt hleftRaw

    rw [hleft]

    have hperiod :
        (u + N - b) % N =
          (u % N + N - b) % N := by
      omega

    rw [hperiod]
    exact (Nat.mod_eq_of_lt hleftRaw)

/--
The value of `a + d - b : Fin N` agrees with the explicit natural-number
residue used by `relativeOverlapOffset`.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by

  have hN : 0 < N := by
    exact Nat.zero_lt_of_lt a.2

  unfold relativeOverlapOffset

  rw [Fin.val_sub]
  rw [Fin.val_add]

  have hbridge :=
    mod_add_period_sub_eq
      (N := N)
      (u := a.val + d.val)
      (b := b.val)
      hN
      b.2

  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbridge

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
