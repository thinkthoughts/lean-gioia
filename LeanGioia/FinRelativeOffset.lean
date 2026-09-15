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

The key arithmetic fact is isolated first: reducing `a + d` modulo `N`
before taking the cyclic difference from `b` gives the same residue as
forming the unreduced natural-number expression and reducing once at
the end.
-/

namespace LeanGioia

/--
Adding a multiple of `N` to the left argument does not change the
remainder modulo `N`.
-/
theorem add_mul_mod_eq_mod
    (x q N : Nat) :
    (x + N * q) % N = x % N := by
  rw [Nat.add_mul_mod_self_left]

/--
Normalize the natural-number encoding of a cyclic difference.

For `b < N`, reducing `u` modulo `N` before forming the cyclic
difference from `b` gives the same residue as forming the difference
from `u` first and reducing afterward.
-/
theorem relativeOffset_mod_normalize
    {N u b : Nat}
    (hN : 0 < N)
    (hb : b < N) :
    (u % N + N - b) % N =
      (u + N - b) % N := by
  have hdecomp :
      u = u % N + N * (u / N) := by
    exact (Nat.mod_add_div u N).symm

  by_cases hbu : b ≤ u % N

  · have hleft :
        u % N + N - b =
          (u % N - b) + N := by
      omega

    have hright :
        u + N - b =
          (u % N - b) + N * (u / N + 1) := by
      rw [hdecomp]
      omega

    rw [hleft, hright]
    rw [Nat.add_mod]
    rw [Nat.mul_mod]
    simp

  · have hbu' :
        u % N < b := by
      omega

    have hleft :
        u % N + N - b =
          N - (b - u % N) := by
      omega

    have hright :
        u + N - b =
          (N - (b - u % N)) + N * (u / N) := by
      rw [hdecomp]
      omega

    rw [hleft, hright]
    rw [Nat.add_mul_mod_self_left]

/--
The value of `a + d - b : Fin N` agrees with the explicit
natural-number cyclic residue used by `relativeOverlapOffset`.
-/
theorem fin_add_sub_val_eq_relativeOverlapOffset
    {N : Nat} (a b d : Fin N) :
    (a + d - b).val =
      relativeOverlapOffset N a.val b.val d.val := by
  unfold relativeOverlapOffset

  have hN :
      0 < N := by
    exact Nat.zero_lt_of_lt a.2

  have hnormalize :
      ((a.val + d.val) % N + N - b.val) % N =
        (a.val + d.val + N - b.val) % N := by
    exact relativeOffset_mod_normalize hN b.2

  simp only [Fin.val_sub, Fin.val_add]

  rw [hnormalize]

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
