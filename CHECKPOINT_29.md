# Checkpoint 29 — pure overlap arithmetic

Checkpoint 29 proves that if `a,b,d < R` and `3R < N`, then

`(a + N + d - b) mod N`

lies either in the forward region `< 2R` or the backward region
`[N-R, N)`.

The next checkpoint proves `CanonicalOffsetComposition`, identifying the
actual cyclic offset with this transported-offset formula.

```bash
lake build
```
