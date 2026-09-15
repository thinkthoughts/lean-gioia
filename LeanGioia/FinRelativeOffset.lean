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
The value of `a + d - b : Fin N` agrees with the explicit
natural-number cyclic residue.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by
  unfold relativeOverlapOffset

  have hN : 0 < N := by
    exact Nat.zero_lt_of_lt a.2

  simp only [Fin.val_sub, Fin.val_add]

  have hab :
      b.val ≤ (a.val + d.val) % N ∨
      (a.val + d.val) % N < b.val := by
    omega

  rcases hab with hab | hab

  · have h₁ :
        N - b.val + (a.val + d.val) % N =
          ((a.val + d.val) % N - b.val) + N := by
      omega

    rw [h₁]
    rw [Nat.add_mod]
    simp

    have hmod :
        ((a.val + d.val) % N - b.val) % N =
          (a.val + d.val + N - b.val) % N := by
      have hlt :
          (a.val + d.val) % N < N :=
        Nat.mod_lt _ hN
      omega

    exact hmod

  · have hlt :
        (a.val + d.val) % N < N :=
      Nat.mod_lt _ hN

    have hraw :
        N - b.val + (a.val + d.val) % N < N := by
      omega

    rw [Nat.mod_eq_of_lt hraw]

    have htarget :
        (a.val + d.val + N - b.val) % N =
          N - b.val + (a.val + d.val) % N := by
      have hsum :
          a.val + d.val =
            (a.val + d.val) % N +
              N * ((a.val + d.val) / N) := by
        exact (Nat.mod_add_div (a.val + d.val) N).symm

      rw [hsum]

      have hrearrange :
          (a.val + d.val) % N +
                N * ((a.val + d.val) / N) +
                N -
                b.val =
            (N - b.val + (a.val + d.val) % N) +
              N * ((a.val + d.val) / N) := by
        omega

      rw [hrearrange]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hraw

    exact htarget.symm

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
