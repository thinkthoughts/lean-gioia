/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Hawkley
-/

/-!
# LeanGioia.WState

Formalization 001: W-state locality obstruction.

Source:
Lei Gioia, Sanjay Moudgalya, and Olexei I. Motrunich,
"Distinct Types of Parent Hamiltonians for Quantum States:
Insights from the W State as a Quantum Many-Body Scar."

Planned primary target:

If the W state is an eigenstate of an extensive-local operator,
then the vacuum state is also an eigenstate.

The exact Lean representation of finite qubit systems, locality,
operators, and eigenstates should be chosen from the source-paper
hypotheses rather than fixed prematurely here.
-/

import LeanGioia.Basic

namespace LeanGioia

/-!
Initial implementation order:

1. finite N-qubit state space;
2. vacuum state;
3. single-excitation basis states and normalized W state;
4. finite-range / extensive-local operator representation;
5. eigenstate predicate or reuse of Mathlib spectral definitions;
6. operator-basis locality lemma;
7. W-eigenstate -> vacuum-eigenstate theorem.

No theorem is stated here yet because `SPEC.md` is the controlling
scientific specification and the faithful operator representation
still needs to be selected.
-/

end LeanGioia
