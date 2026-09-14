# Checkpoint 24 — exact periodic overlap hull

Checkpoint 24 replaces the supplied `overlap_localizes` field with an
exactly defined periodic overlap hull.

A same-start `3R` block is orientation-sensitive: an overlapping block can
begin to the left of the selected support. Rather than prove a false
containment statement, the exact hull is defined as all sites lying in a
range-`R` block that overlaps the selected range-`R` block.

Lean then proves directly:

```text
overlapping competing block
→ competing block ⊆ overlapInteraction.
```

The remaining geometry is only the quantitative bound on the exact hull:

```text
card (overlapInteraction N R s) < N
```

The next checkpoint can derive that from the paper's `3R < N` condition.

Run:

```bash
lake build
```
