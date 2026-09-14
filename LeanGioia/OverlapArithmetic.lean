import LeanGioia.OverlapCoordinates

/-!
# LeanGioia.OverlapArithmetic

Checkpoint 29: prove the pure natural-number arithmetic behind the
periodic overlap cover.
-/

namespace LeanGioia

def relativeOverlapOffset (N a b d : Nat) : Nat :=
  (a + N + d - b) % N

theorem relativeOverlapOffset_forward_or_backward
    {N R a b d : Nat}
    (hNR : 3 * R < N)
    (ha : a < R)
    (hb : b < R)
    (hd : d < R) :
    relativeOverlapOffset N a b d < 2 * R ∨
      N - R ≤ relativeOverlapOffset N a b d := by
  unfold relativeOverlapOffset
  have hrawUpper : a + N + d - b < 2 * N := by omega
  have hrawLower : N - R ≤ a + N + d - b := by omega
  by_cases hraw : a + N + d - b < N
  · right
    rw [Nat.mod_eq_of_lt hraw]
    exact hrawLower
  · left
    have hNle : N ≤ a + N + d - b := by omega
    rw [Nat.mod_eq_sub_mod hNle]
    have hsubLt : a + N + d - b - N < N := by omega
    rw [Nat.mod_eq_of_lt hsubLt]
    omega

def InThreeRCoverRegion
    {N : Nat} (R : Nat) (start x : Fin N) : Prop :=
  cyclicOffset N start x < 2 * R ∨
    N - R ≤ cyclicOffset N start x

def CanonicalOffsetComposition (N R : Nat) : Prop :=
  ∀ (start x : Fin N)
    (h : CanonicalOverlapCoordinates N R start x),
    cyclicOffset N start x =
      relativeOverlapOffset N
        (cyclicOffset N start h.shared)
        (cyclicOffset N h.competitorStart h.shared)
        (cyclicOffset N h.competitorStart x)

theorem canonicalOverlap_in_threeR_region
    {N R : Nat}
    (hNR : 3 * R < N)
    (hcomp : CanonicalOffsetComposition N R)
    (start x : Fin N)
    (h : CanonicalOverlapCoordinates N R start x) :
    InThreeRCoverRegion R start x := by

  have hsplit :=
    relativeOverlapOffset_forward_or_backward
      hNR
      h.shared_from_selected_lt
      h.shared_from_competitor_lt
      h.x_from_competitor_lt

  unfold InThreeRCoverRegion

  rw [hcomp start x h]

  exact hsplit

def CanonicalOverlapInThreeRRegion (N R : Nat) : Prop :=
  ∀ (start x : Fin N),
    CanonicalOverlapCoordinates N R start x →
      InThreeRCoverRegion R start x

theorem canonicalOverlapInThreeRRegion_of_composition
    {N R : Nat}
    (hNR : 3 * R < N)
    (hcomp : CanonicalOffsetComposition N R) :
    CanonicalOverlapInThreeRRegion N R := by
  intro start x h
  exact canonicalOverlap_in_threeR_region hNR hcomp start x h

end LeanGioia
