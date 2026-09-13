import LeanGioia.PureCreation

/-!
# LeanGioia.Cancellation

Checkpoint 5: uncancellable-witness lemma from Appendix C.1.a.

The source paper's finite-range argument chooses a higher-particle basis
configuration produced by a selected pure-creation term and argues that,
because the extra occupied site is sufficiently far from the term's local
support, no other range-`R` term can cancel that amplitude.

This file formalizes the cancellation logic once such a witness has been
identified.  The next checkpoint will construct the witness from the
periodic-chain range assumptions (`N > 3R` in the Appendix C argument).
-/

namespace LeanGioia

/--
A basis configuration is outside the W sector exactly for the purpose
needed by the cancellation argument: the W amplitude there vanishes.
-/
def IsOutsideWSector {N : ℕ} (b : Bitstring N) : Prop :=
  wState N b = 0

/--
An operator contribution `T` has an uncancellable witness `b` relative to a
remainder contribution if:

* `b` lies outside the W sector;
* `T |W⟩` has nonzero amplitude at `b`;
* the remainder has zero amplitude at `b`.

This packages the logical content of the "cannot be cancelled by any other
range-R term" step in Appendix C.1.a without yet assuming a particular
encoding of periodic distance.
-/
structure UncancellableWitness {N : ℕ}
    (T : Operator N) (remainder : State N) where
  basis : Bitstring N
  outsideW : IsOutsideWSector basis
  target_nonzero : T (wState N) basis ≠ 0
  remainder_zero : remainder basis = 0

/--
Coefficient extraction from an uncancellable witness.

If `G |W⟩` is, coefficientwise, the selected contribution
`c * T |W⟩` plus a remainder, and the witness basis state receives no
remainder amplitude, then the W-eigenstate equation forces `c = 0`.
-/
theorem coefficient_zero_of_uncancellable_witness {N : ℕ}
    (G T : Operator N) (remainder : State N) (c eig : ℂ)
    (w : UncancellableWitness T remainder)
    (hdecomp :
      G (wState N) w.basis =
        c * T (wState N) w.basis + remainder w.basis)
    (hEig : IsEigenstate G (wState N) eig) :
    c = 0 := by
  have heq :
      G (wState N) w.basis = eig * wState N w.basis :=
    (isEigenstate_iff_amplitudes G (wState N) eig).mp hEig w.basis
  rw [w.outsideW, mul_zero] at heq
  rw [heq, w.remainder_zero, add_zero] at hdecomp
  have hz : c * T (wState N) w.basis = 0 := hdecomp.symm
  exact (mul_eq_zero.mp hz).resolve_right w.target_nonzero

/--
A direct version of the same cancellation lemma, useful while constructing
the periodic-chain witness in the next checkpoint.
-/
theorem coefficient_zero_of_unique_amplitude {N : ℕ}
    (G T : Operator N) (b : Bitstring N) (c eig : ℂ)
    (hOutside : wState N b = 0)
    (hTarget : T (wState N) b ≠ 0)
    (hAmplitude : G (wState N) b = c * T (wState N) b)
    (hEig : IsEigenstate G (wState N) eig) :
    c = 0 := by
  have heq :
      G (wState N) b = eig * wState N b :=
    (isEigenstate_iff_amplitudes G (wState N) eig).mp hEig b
  rw [hOutside, mul_zero] at heq
  rw [heq] at hAmplitude
  have hz : c * T (wState N) b = 0 := hAmplitude.symm
  exact (mul_eq_zero.mp hz).resolve_right hTarget

end LeanGioia
