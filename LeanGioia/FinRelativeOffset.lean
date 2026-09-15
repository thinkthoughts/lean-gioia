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
expressions inline in the main theorem.
-/

namespace LeanGioia

/--
Adding a full modulus before subtracting `b` gives the same residue
whether `u` is reduced modulo `N` first or afterward.

Proved by introducing the `Nat.div_add_mod` witness for `u` once, up
front, so the rest of the identity is pure linear arithmetic that
`omega` can close directly — no case split, and no separate `% N`
terms left for `omega` to relate on its own.
-/
theorem relative_mod_sub
    {N u b : Nat}
    (_hN : 0 < N)
    (hb : b < N) :
    (N - b + u % N) % N =
      (u + N - b) % N := by
  have hdm : N * (u / N) + u % N = u := Nat.div_add_mod u N
  have hkey :
      u + N - b = (N - b + u % N) + N * (u / N) := by
    omega
  rw [hkey, Nat.add_mul_mod_self_left]

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
