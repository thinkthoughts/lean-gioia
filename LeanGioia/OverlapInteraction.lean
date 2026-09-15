import LeanGioia.PeriodicRange

/-!
# LeanGioia.OverlapInteraction

Foundational definition of the exact periodic overlap interaction hull.

This declaration originated in Checkpoint 24 and is kept below the
cyclic-offset and overlap-coordinate layers so that later checkpoints
can depend on it without creating an import cycle.
-/

namespace LeanGioia

/--
The exact periodic interaction hull of the selected range-`R` block.
-/
def overlapInteraction
    (N R : Nat) (selectedStart : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun x =>
    ∃ competitorStart : Fin N,
      ¬ Disjoint
        (cyclicBlock N R competitorStart)
        (cyclicBlock N R selectedStart) ∧
      x ∈ cyclicBlock N R competitorStart

/--
Every selected-block site lies in its overlap interaction hull.
-/
theorem cyclicBlock_subset_overlapInteraction
    {N R : Nat} (selectedStart : Fin N) :
    cyclicBlock N R selectedStart ⊆
      overlapInteraction N R selectedStart := by
  intro x hx
  simp only [overlapInteraction, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine ⟨selectedStart, ?_, hx⟩
  intro hdis
  exact (Finset.disjoint_left.mp hdis) hx hx

/--
Any overlapping range-`R` cyclic block is contained in the exact
overlap interaction hull.
-/
theorem cyclicBlock_subset_overlapInteraction_of_overlap
    {N R : Nat} {selectedStart competitorStart : Fin N}
    (hoverlap :
      ¬ Disjoint
        (cyclicBlock N R competitorStart)
        (cyclicBlock N R selectedStart)) :
    cyclicBlock N R competitorStart ⊆
      overlapInteraction N R selectedStart := by
  intro x hx
  simp only [overlapInteraction, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨competitorStart, hoverlap, hx⟩

end LeanGioia
