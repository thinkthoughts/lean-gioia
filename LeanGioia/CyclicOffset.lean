import LeanGioia.PeriodicOverlapContainment

/-!
# LeanGioia.CyclicOffset

Checkpoint 27: introduce a canonical cyclic offset and connect it to the
existing `cyclicBlock` representation.

For `start, x : Fin N`, define the clockwise offset

`cyclicOffset N start x = (x + N - start) mod N`.

This file proves the basic facts needed for the final overlap arithmetic:

1. the offset is always `< N`;
2. adding the offset back to `start` recovers `x` modulo `N`;
3. for a block width `≤ N`, membership in `cyclicBlock` is equivalent to
   the cyclic offset being smaller than the width.

This turns the remaining overlap proof into inequalities between ordinary
natural-number offsets rather than repeated equalities of modular
expressions.
-/

namespace LeanGioia

/-- Clockwise periodic offset from `start` to `x`. -/
def cyclicOffset
    (N : Nat) (start x : Fin N) : Nat :=
  (x.1 + N - start.1) % N

/-- A cyclic offset is a valid residue. -/
theorem cyclicOffset_lt
    {N : Nat} (start x : Fin N) :
    cyclicOffset N start x < N := by
  unfold cyclicOffset
  have hstart : start.1 < N := start.2
  have hN : 0 < N := by
    omega
  exact Nat.mod_lt _ hN

/-- The cyclic offset from a site to itself is zero. -/
@[simp]
theorem cyclicOffset_self
    {N : Nat} (start : Fin N) :
    cyclicOffset N start start = 0 := by
  unfold cyclicOffset
  have hstart : start.1 < N := start.2
  have hraw : start.1 + N - start.1 = N := by
    omega
  rw [hraw]
  exact Nat.mod_self N

/--
Adding the canonical cyclic offset back to `start` recovers `x`.
-/
theorem cyclicOffset_spec
    {N : Nat} (start x : Fin N) :
    x.1 = (start.1 + cyclicOffset N start x) % N := by
  have hstart : start.1 < N := start.2
  have hx : x.1 < N := x.2
  have hN : 0 < N := by
    omega
  by_cases hle : start.1 ≤ x.1
  · have hraw :
        x.1 + N - start.1 = (x.1 - start.1) + N := by
      omega
    have hoff :
        cyclicOffset N start x = x.1 - start.1 := by
      unfold cyclicOffset
      rw [hraw]
      simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : x.1 - start.1 < N)]
    rw [hoff]
    have hadd : start.1 + (x.1 - start.1) = x.1 := by
      omega
    rw [hadd]
    exact (Nat.mod_eq_of_lt hx).symm
  · have hlt : x.1 < start.1 := by
      omega
    have hrawlt :
        x.1 + N - start.1 < N := by
      omega
    have hoff :
        cyclicOffset N start x = x.1 + N - start.1 := by
      unfold cyclicOffset
      exact Nat.mod_eq_of_lt hrawlt
    rw [hoff]
    have hadd :
        start.1 + (x.1 + N - start.1) = x.1 + N := by
      omega
    rw [hadd]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hx]

/--
Membership in a cyclic block of width at most `N` implies that the
canonical cyclic offset is below that width.
-/
theorem cyclicOffset_lt_of_mem_cyclicBlock
    {N width : Nat} {start x : Fin N}
    (hwidth : width ≤ N)
    (hx : x ∈ cyclicBlock N width start) :
    cyclicOffset N start x < width := by
  rcases mem_cyclicBlock_iff.mp hx with ⟨t, ht, hxt⟩
  have htN : t < N := lt_of_lt_of_le ht hwidth
  have hs : start.1 < N := start.2
  have hN : 0 < N := by
    omega
  by_cases hsum : start.1 + t < N
  · have hxval : x.1 = start.1 + t := by
      rw [hxt, Nat.mod_eq_of_lt hsum]
    have hraw :
        x.1 + N - start.1 = t + N := by
      omega
    unfold cyclicOffset
    rw [hraw]
    simp [Nat.add_mod, Nat.mod_eq_of_lt htN, ht]
  · have hNsum : N ≤ start.1 + t := by
      omega
    have hsum2 : start.1 + t < 2 * N := by
      omega
    have hmod :
        (start.1 + t) % N = start.1 + t - N := by
      rw [Nat.mod_eq_sub_mod hNsum]
      exact Nat.mod_eq_of_lt (by omega)
    have hxval : x.1 = start.1 + t - N := by
      rw [hxt, hmod]
    have hraw :
        x.1 + N - start.1 = t := by
      omega
    unfold cyclicOffset
    rw [hraw]
    have hmodt : t % N = t := Nat.mod_eq_of_lt htN
    rw [hmodt]
    exact ht

/--
Conversely, an offset smaller than `width` gives membership in the cyclic
block.
-/
theorem mem_cyclicBlock_of_cyclicOffset_lt
    {N width : Nat} {start x : Fin N}
    (h : cyclicOffset N start x < width) :
    x ∈ cyclicBlock N width start := by
  apply mem_cyclicBlock_iff.mpr
  refine ⟨cyclicOffset N start x, h, ?_⟩
  exact cyclicOffset_spec start x

/--
For widths bounded by the chain size, cyclic-block membership is exactly
the canonical offset inequality.
-/
theorem mem_cyclicBlock_iff_cyclicOffset_lt
    {N width : Nat} {start x : Fin N}
    (hwidth : width ≤ N) :
    x ∈ cyclicBlock N width start ↔
      cyclicOffset N start x < width := by
  constructor
  · exact cyclicOffset_lt_of_mem_cyclicBlock hwidth
  · exact mem_cyclicBlock_of_cyclicOffset_lt

end LeanGioia
