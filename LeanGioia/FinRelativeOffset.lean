import LeanGioia.OffsetComposition

/-!
# LeanGioia.FinRelativeOffset

Checkpoint 31: close the representation bridge between `Fin N`
group arithmetic and the natural-number residue expression used in
Checkpoint 29.

Checkpoint 30 proved the group-level identity in `Fin N` and reduced the
remaining work to `FinRelativeOffsetValueBridge N`.

The value of `a + d - b : Fin N` normalizes to

`(N - b.val + ((a.val + d.val) % N)) % N`.

The target representation is

`(a.val + N + d.val - b.val) % N`.

This checkpoint proves their equality by splitting on the ordinary
subtraction boundary `b.val ≤ a.val + d.val`.
-/

namespace LeanGioia

/--
The value of `a + d - b : Fin N` agrees with the explicit natural-number
residue used by `relativeOverlapOffset`.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by
  have hN : 0 < N := by
    omega
  haveI : NeZero N := ⟨Nat.ne_of_gt hN⟩

  unfold relativeOverlapOffset
  simp only [Fin.val_sub, Fin.val_add]

  have ha : a.val < N := a.2
  have hb : b.val < N := b.2
  have hd : d.val < N := d.2

  by_cases hsum : a.val + d.val < N

  · rw [Nat.mod_eq_of_lt hsum]

    have hraw :
        N - b.val + (a.val + d.val) =
          a.val + N + d.val - b.val := by
      omega

    rw [hraw]

  · have hNle : N ≤ a.val + d.val := by
      omega

    have hsum2N :
        a.val + d.val < 2 * N := by
      omega

    have hmod :
        (a.val + d.val) % N =
          a.val + d.val - N := by
      rw [Nat.mod_eq_sub_mod hNle]
      have hlt :
          a.val + d.val - N < N := by
        omega
      exact Nat.mod_eq_of_lt hlt

    rw [hmod]

    have hleft :
        N - b.val + (a.val + d.val - N) =
          a.val + d.val - b.val := by
      omega

    rw [hleft]

    have hright :
        a.val + N + d.val - b.val =
          N + (a.val + d.val - b.val) := by
      omega

    rw [hright]

    simp

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
